module
public import Submission.CatalanMeasure.GenD.RankFilt
@[expose] public section

/-!
# Block-rank framework for Theorems U6g and S (GenD)

If a family of `m` linear functionals `φ` on the row combinations forces every digit of `Qh` and
`Dh` to vanish on the residues `[m0, m1)`, then the filtered matrix has rank at most
`n - (nJ * (m1 - m0) - m)`: the `nJ * (m1 - m0)` block columns `J p + mu - (b+q)` are killed by
the digit formula, and every other column is imposed to vanish at the cost of one constraint.
-/

namespace CatalanMeasure.GenD
open Polynomial OAI.InternalCatalan CatalanMeasure.Parametric
noncomputable section

theorem div_mod_pair {p a b a' b' : ℕ} (hp0 : 0 < p) (hb : b < p) (hb' : b' < p)
    (h : a * p + b = a' * p + b') : a = a' ∧ b = b' := by
  have e1 : (a * p + b) / p = a := by
    rw [mul_comm, Nat.mul_add_div hp0, Nat.div_eq_of_lt hb, add_zero]
  have e2 : (a' * p + b') / p = a' := by
    rw [mul_comm, Nat.mul_add_div hp0, Nat.div_eq_of_lt hb', add_zero]
  have ha : a = a' := by rw [← e1, ← e2, h]
  subst ha
  exact ⟨rfl, by omega⟩

/-- The block columns. -/
def blockCols (b q p J0 nJ m0 m1 : ℕ) : Finset ℕ :=
  (Finset.Ico J0 (J0 + nJ) ×ˢ Finset.Ico m0 m1).image fun x => x.1 * p + x.2 - (b + q)

theorem blockCols_card {b q p J0 nJ m0 m1 : ℕ} (hp0 : 0 < p) (hm1 : m1 ≤ p)
    (hk0 : ∀ J mu, J0 ≤ J → J < J0 + nJ → m0 ≤ mu → mu < m1 → b + q ≤ J * p + mu) :
    (blockCols b q p J0 nJ m0 m1).card = nJ * (m1 - m0) := by
  unfold blockCols
  rw [Finset.card_image_of_injOn, Finset.card_product, Nat.card_Ico, Nat.card_Ico]
  · simp
  · rintro ⟨J, mu⟩ hx ⟨J', mu'⟩ hy hxy
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_Ico, Set.mem_Ico] at hx hy
    simp only at hxy
    have a1 := hk0 J mu hx.1.1 hx.1.2 hx.2.1 hx.2.2
    have a2 := hk0 J' mu' hy.1.1 hy.1.2 hy.2.1 hy.2.2
    have := div_mod_pair hp0 (b := mu) (b' := mu') (a := J) (a' := J') (by omega) (by omega)
      (by omega)
    rw [this.1, this.2]

theorem blockCols_subset {b q p J0 nJ m0 m1 n : ℕ}
    (hk1 : ∀ J mu, J0 ≤ J → J < J0 + nJ → m0 ≤ mu → mu < m1 → J * p + mu - (b + q) < n) :
    blockCols b q p J0 nJ m0 m1 ⊆ Finset.range n := by
  intro k hk
  unfold blockCols at hk
  obtain ⟨⟨J, mu⟩, hx, rfl⟩ := Finset.mem_image.mp hk
  simp only [Finset.mem_product, Finset.mem_Ico] at hx
  exact Finset.mem_range.mpr (hk1 J mu hx.1.1 hx.1.2 hx.2.1 hx.2.2)

section
variable {P : Parameters} {N p : ℕ} [hp : Fact p.Prime]

/-- Number of constraints in the two families. -/
abbrev blockCost (fc m : ℕ) : Fin 2 → ℕ
  | 0 => fc
  | 1 => m

/-- The two constraint families: free columns vanish, and the digit functionals vanish. -/
def blockConstraint (P : Parameters) (N p : ℕ) [Fact p.Prime] (free : Finset ℕ) (m : ℕ)
    (φ : Fin m → (Fin (P.n N) → ZMod p) →ₗ[ZMod p] ZMod p) :
    ∀ i : Fin 2, (Fin (P.n N) → ZMod p) →ₗ[ZMod p] (Fin (blockCost free.card m i) → ZMod p)
  | 0 => LinearMap.pi fun a : Fin free.card => fResp P N p (free.orderEmbOfFin rfl a)
  | 1 => LinearMap.pi φ

/-- A column in the block has the digit decomposition `(J, mu)`. -/
theorem block_col_digit {b q p J mu : ℕ} (hp0 : 0 < p) (hq : q ≤ mu) (hmu : mu < p)
    (hk : b + q ≤ J * p + mu) :
    (b + (J * p + mu - (b + q))) % p + q = mu := by
  have e : b + (J * p + mu - (b + q)) = (mu - q) + J * p := by omega
  rw [e, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
  omega

theorem block_col_div {b q p J mu : ℕ} (hp0 : 0 < p) (hq : q ≤ mu) (hmu : mu < p)
    (hk : b + q ≤ J * p + mu) :
    (b + (J * p + mu - (b + q))) / p = J := by
  have e : b + (J * p + mu - (b + q)) = (mu - q) + J * p := by omega
  rw [e, Nat.add_mul_div_right _ _ hp0, Nat.div_eq_of_lt (by omega)]
  omega

/-- **Block rank bound.** -/
theorem rank_of_digit_block (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2)
    (hH : P.H N < p ^ 2) {J0 nJ m0 m1 : ℕ}
    (hq : P.q N ≤ m0) (hm1 : m1 ≤ p)
    (hk0 : ∀ J mu, J0 ≤ J → J < J0 + nJ → m0 ≤ mu → mu < m1 → P.b N + P.q N ≤ J * p + mu)
    (hk1 : ∀ J mu, J0 ≤ J → J < J0 + nJ → m0 ≤ mu → mu < m1 →
      J * p + mu - (P.b N + P.q N) < P.n N)
    {m : ℕ} (φ : Fin m → (Fin (P.n N) → ZMod p) →ₗ[ZMod p] ZMod p)
    (hφ : ∀ c : Fin (P.n N) → ZMod p, (∀ a, φ a c = 0) → ∀ mu, m0 ≤ mu → mu < m1 → ∀ u,
      (qhP P N p c).coeff (u * p + mu) = 0 ∧ (dhP P N p c).coeff (u * p + mu) = 0) :
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val)).rank +
        (nJ * (m1 - m0) - m) ≤ P.n N := by
  have hp0 := hp.out.pos
  set blk := blockCols (P.b N) (P.q N) p J0 nJ m0 m1 with hblk
  have hcard : blk.card = nJ * (m1 - m0) := blockCols_card hp0 hm1 hk0
  have hsub : blk ⊆ Finset.range (P.n N) := blockCols_subset hk1
  set free := Finset.range (P.n N) \ blk with hfree
  have hfc : free.card = P.n N - blk.card := by
    rw [hfree, Finset.card_sdiff_of_subset hsub, Finset.card_range]
  have hblc : blk.card ≤ P.n N := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_range] at this
  let J : LinearMap.ker (secondaryTentConstraintMap (blockCost free.card m)
      (blockConstraint P N p free m φ)) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
    Submodule.subtype _
  have hr := secondaryTent_rank_of_constraints
    (scaledResidueMatrix (p := p)
      (Matrix.of fun r k : Fin (P.n N) => filteredEntryRat P 0 N r.val k.val))
    (blockCost free.card m) (blockConstraint P N p free m φ) J Subtype.val_injective (by
      intro v
      have hv := (secondaryTentConstraintMap_eq_zero_iff _ _ v.1).mp v.2
      funext k
      rw [fResp_eq_mulVec]
      by_cases hkb : k.val ∈ blk
      · obtain ⟨⟨Jc, mu⟩, hx, hxk⟩ := Finset.mem_image.mp hkb
        simp only [Finset.mem_product, Finset.mem_Ico] at hx
        have hk0' := hk0 Jc mu hx.1.1 hx.1.2 hx.2.1 hx.2.2
        have hkeq : k.val = Jc * p + mu - (P.b N + P.q N) := hxk.symm
        have hd := block_col_digit (b := P.b N) (q := P.q N) (J := Jc) (mu := mu) hp0
          (by omega) (by omega) hk0'
        rw [← hkeq] at hd
        have hdig := hφ v.1 (fun a => by
          have := congrFun (hv 1) a
          simpa [blockConstraint, LinearMap.pi_apply] using this) mu hx.2.1 hx.2.2
        refine fResp_eq_zero hP hN hp2 hH k.isLt (by rw [hd]; omega) v.1 ?_ ?_
        · intro u _; rw [hd]; exact (hdig u).1
        · intro u _; rw [hd]; exact (hdig u).2
      · have hkf : k.val ∈ free := by
          rw [hfree]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr k.isLt, hkb⟩
        have hmem : ∃ a : Fin free.card, free.orderEmbOfFin rfl a = k.val := by
          have := (Finset.range_orderEmbOfFin free rfl)
          have hk' : k.val ∈ Set.range (free.orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]; exact hkf
          exact hk'
        obtain ⟨a, ha⟩ := hmem
        have := congrFun (hv 0) a
        simp only [blockConstraint, LinearMap.pi_apply, Pi.zero_apply] at this
        rw [ha] at this
        exact this)
  rw [Module.finrank_fin_fun] at hr
  have hsum : ∑ i, blockCost free.card m i = free.card + m := by
    simp [Fin.sum_univ_succ, blockCost]
  rw [hsum, hfc, hcard] at hr
  omega

end
end
end CatalanMeasure.GenD
