module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger.Instance

@[expose] public section
set_option Elab.async false

/-!
# Generic lower bound for the H' + P sum on a fixed digit/block choice (lane G5e)

`hpsKap_ge`: if both applicability conditions hold at `(s, k0, k1, ilo)` and the digit sets of the
two families have at most `cH`, `cP` elements, then
`mH * (hpD - hpElo) + mP * (Pmax - ilo + 1)` is below `hpsKap`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger2
open CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.Slots CatalanMeasure.GenD.Uniform.Bank540.Ledger
noncomputable section

theorem hpsVal_le_hpsKap (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) (ilo : ℕ)
    (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0) (h01 : k0 ≤ k1) (h1 : k1 ≤ hpKmax P N p)
    (hilo : ilo ≤ hpEta P N p s) :
    hpVal P N p s k0 k1 + perVal P N p s k0 k1 ilo ≤ hpsKap P N p := by
  unfold hpsKap
  refine le_trans ?_ (Finset.le_sup (f := fun s =>
      (Finset.Icc (hpKmin P N p) (hpKmax P N p)).sup fun k0 =>
        (Finset.Icc k0 (hpKmax P N p)).sup fun k1 =>
          (Finset.range (hpEta P N p s + 1)).sup fun ilo =>
            hpVal P N p s k0 k1 + perVal P N p s k0 k1 ilo)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hs)))
  refine le_trans ?_ (Finset.le_sup (f := fun k0 =>
      (Finset.Icc k0 (hpKmax P N p)).sup fun k1 =>
        (Finset.range (hpEta P N p s + 1)).sup fun ilo =>
          hpVal P N p s k0 k1 + perVal P N p s k0 k1 ilo)
    (Finset.mem_Icc.mpr ⟨h0, h01.trans h1⟩))
  refine le_trans ?_ (Finset.le_sup (f := fun k1 =>
      (Finset.range (hpEta P N p s + 1)).sup fun ilo =>
        hpVal P N p s k0 k1 + perVal P N p s k0 k1 ilo)
    (Finset.mem_Icc.mpr ⟨h01, h1⟩))
  exact Finset.le_sup (f := fun ilo => hpVal P N p s k0 k1 + perVal P N p s k0 k1 ilo)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hilo))

theorem hpsKap_ge {P : Parameters} {N p s : ℕ} {k0 k1 : ℤ} {ilo cH cP mH mP : ℕ}
    (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0) (h01 : k0 ≤ k1) (h1 : k1 ≤ hpKmax P N p)
    (hilo : ilo ≤ hpEta P N p s)
    (hOKH : hpOK P N p s k0 k1) (hOKP : perOK P N p s k0 k1 ilo)
    (hcH : (hpJJ P N p s k0 k1).card ≤ cH) (hcP : (perJJ P N p s k0 k1 ilo).card ≤ cP)
    (hmH : mH + cH ≤ hpK k0 k1 + 1) (hmH' : mH ≤ hpK k0 k1) (hmP : mP + cP ≤ hpK k0 k1) :
    mH * (hpD P N p s k0 k1 - hpElo P N p s) +
      mP * ((perPmax P N p s k0 k1).toNat - ilo + 1) ≤ hpsKap P N p := by
  refine le_trans ?_ (hpsVal_le_hpsKap P N p s k0 k1 ilo hs h0 h01 h1 hilo)
  unfold hpVal perVal
  rw [if_pos hOKH, if_pos hOKP]
  exact Nat.add_le_add (Nat.mul_le_mul_right _ (le_min hmH' (by omega)))
    (Nat.mul_le_mul_right _ (by omega))

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger2
