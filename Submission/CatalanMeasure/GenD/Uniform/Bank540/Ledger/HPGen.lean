module

public import Submission.CatalanMeasure.GenD.Uniform.Bank540.Ledger.Cells
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HPSLB

@[expose] public section
set_option Elab.async false

/-!
# Generic lower-bound lemmas for the H' and P families on a fixed digit/block choice (G5c)

`hpKap_ge` / `perKap_ge`: if `(s,k0,k1)` is in range, the applicability condition holds and the
digit set `JJ` has at most `c` elements, then `m0 * (slots)` is below `hpKap` (`perKap`).
`spread_card` bounds the card of a set of digits from the spread of `J * p`.
-/

namespace CatalanMeasure.GenD.Uniform.Bank540.Ledger
open CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
open CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section

theorem spread_card {S : Finset ℕ} {p c : ℕ} (hp : 0 < p)
    (h : ∀ x ∈ S, ∀ y ∈ S, x * p < y * p + c * p) : S.card ≤ c := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · set y0 := S.min' hne with hy0
    have hy : y0 ∈ S := S.min'_mem hne
    have hlt : ∀ x ∈ S, x < y0 + c := by
      intro x hx
      have := h x hx y0 hy
      have h2 : x * p < (y0 + c) * p := by rw [add_mul]; exact this
      exact lt_of_mul_lt_mul_right h2 (Nat.zero_le _)
    have hsub : S ⊆ Finset.Ico y0 (y0 + c) := by
      intro x hx
      exact Finset.mem_Ico.mpr ⟨S.min'_le x hx, hlt x hx⟩
    calc S.card ≤ (Finset.Ico y0 (y0 + c)).card := Finset.card_le_card hsub
      _ = c := by simp

theorem interval_card {S : Finset ℕ} {lo hi : ℕ} (h : ∀ x ∈ S, lo ≤ x ∧ x ≤ hi) :
    S.card ≤ hi + 1 - lo := by
  have hsub : S ⊆ Finset.Icc lo hi := fun x hx => Finset.mem_Icc.mpr (h x hx)
  calc S.card ≤ (Finset.Icc lo hi).card := Finset.card_le_card hsub
    _ = hi + 1 - lo := by simp

theorem hpKap_ge {P : Parameters} {N p s : ℕ} {k0 k1 : ℤ} {c m0 : ℕ}
    (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0) (h01 : k0 ≤ k1) (h1 : k1 ≤ hpKmax P N p)
    (hOK : hpOK P N p s k0 k1) (hcard : (hpJJ P N p s k0 k1).card ≤ c)
    (hm : m0 + c ≤ hpK k0 k1 + 1) (hm' : m0 ≤ hpK k0 k1) :
    m0 * (hpD P N p s k0 k1 - hpElo P N p s) ≤ hpKap P N p := by
  refine le_trans ?_ (hpVal_le_hpKap P N p s k0 k1 hs h0 h01 h1)
  unfold hpVal
  rw [if_pos hOK]
  exact Nat.mul_le_mul_right _ (le_min hm' (by omega))

theorem perKap_ge {P : Parameters} {N p s : ℕ} {k0 k1 : ℤ} {ilo c m0 : ℕ}
    (hs : s ≤ P.H N / p) (h0 : hpKmin P N p ≤ k0) (h01 : k0 ≤ k1) (h1 : k1 ≤ hpKmax P N p)
    (hilo : ilo ≤ hpEta P N p s)
    (hOK : perOK P N p s k0 k1 ilo) (hcard : (perJJ P N p s k0 k1 ilo).card ≤ c)
    (hm : m0 + c ≤ hpK k0 k1) :
    m0 * ((perPmax P N p s k0 k1).toNat - ilo + 1) ≤ perKap P N p := by
  have hle : perVal P N p s k0 k1 ilo ≤ perKap P N p := by
    unfold perKap
    refine le_trans ?_ (Finset.le_sup (f := fun s =>
      (Finset.Icc (hpKmin P N p) (hpKmax P N p)).sup fun k0 =>
        (Finset.Icc k0 (hpKmax P N p)).sup fun k1 =>
          (Finset.range (hpEta P N p s + 1)).sup fun ilo => perVal P N p s k0 k1 ilo)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hs)))
    refine le_trans ?_ (Finset.le_sup (f := fun k0 =>
      (Finset.Icc k0 (hpKmax P N p)).sup fun k1 =>
        (Finset.range (hpEta P N p s + 1)).sup fun ilo => perVal P N p s k0 k1 ilo)
      (Finset.mem_Icc.mpr ⟨h0, h01.trans h1⟩))
    refine le_trans ?_ (Finset.le_sup (f := fun k1 =>
        (Finset.range (hpEta P N p s + 1)).sup fun ilo => perVal P N p s k0 k1 ilo)
      (Finset.mem_Icc.mpr ⟨h01, h1⟩))
    exact Finset.le_sup (f := fun ilo => perVal P N p s k0 k1 ilo)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hilo))
  refine le_trans ?_ hle
  unfold perVal
  rw [if_pos hOK]
  exact Nat.mul_le_mul_right _ (by omega)

end
end CatalanMeasure.GenD.Uniform.Bank540.Ledger
