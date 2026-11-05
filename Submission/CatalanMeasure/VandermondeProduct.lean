module

public import Submission.CatalanMeasure.GenVandermondeSharp

@[expose] public section

open Polynomial Finset Matrix

namespace CatalanMeasure

/-- Keep each node's contribution to the coefficient norm. -/
theorem newtonBasis_l1_product (σ : ℕ → ℝ) (hσ : ∀ k, 0 ≤ σ k) (k M : ℕ) :
    ∑ a ∈ range M, |(newtonBasis σ k).coeff a| ≤ ∏ j ∈ range k, (1 + σ j) := by
  induction k generalizing M with
  | zero =>
    cases M <;> simp [newtonBasis, sum_range_succ', coeff_one]
  | succ k ih =>
    rw [newtonBasis_succ, prod_range_succ]
    cases M with
    | zero =>
      simp only [range_zero, sum_empty]
      exact mul_nonneg (prod_nonneg (fun j _ => by linarith [hσ j])) (by linarith [hσ k])
    | succ M =>
      have hshift : ∑ a ∈ range M, |(newtonBasis σ k).coeff a| ≤
          ∑ a ∈ range (M + 1), |(newtonBasis σ k).coeff a| :=
        sum_le_sum_of_subset_of_nonneg (range_mono (by omega)) (fun _ _ _ => abs_nonneg _)
      have hco : ∀ a, |(newtonBasis σ k * (X - C (σ k))).coeff (a + 1)| ≤
          |(newtonBasis σ k).coeff a| + |(newtonBasis σ k).coeff (a + 1)| * σ k := by
        intro a
        rw [coeff_mul_X_sub_C]
        simpa [abs_mul, abs_of_nonneg (hσ k)] using
          abs_sub ((newtonBasis σ k).coeff a) ((newtonBasis σ k).coeff (a + 1) * σ k)
      have h0 : |(newtonBasis σ k * (X - C (σ k))).coeff 0| =
          |(newtonBasis σ k).coeff 0| * σ k := by
        rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub,
          mul_neg, abs_neg, abs_mul, abs_of_nonneg (hσ k)]
      have hs := sum_le_sum (s := range M) (fun a _ => hco a)
      rw [sum_add_distrib, ← sum_mul] at hs
      have he : |(newtonBasis σ k).coeff 0| +
          ∑ a ∈ range M, |(newtonBasis σ k).coeff (a + 1)| =
          ∑ a ∈ range (M + 1), |(newtonBasis σ k).coeff a| := by
        rw [sum_range_succ']; ring
      have hsum : ∑ a ∈ range (M + 1), |(newtonBasis σ k * (X - C (σ k))).coeff a| ≤
          (∑ a ∈ range M, |(newtonBasis σ k).coeff a|) +
            (∑ a ∈ range (M + 1), |(newtonBasis σ k).coeff a|) * σ k := by
        rw [sum_range_succ', h0]
        calc
          (∑ a ∈ range M, |(newtonBasis σ k * (X - C (σ k))).coeff (a + 1)|) +
              |(newtonBasis σ k).coeff 0| * σ k
              ≤ ((∑ a ∈ range M, |(newtonBasis σ k).coeff a|) +
                (∑ a ∈ range M, |(newtonBasis σ k).coeff (a + 1)|) * σ k) +
                  |(newtonBasis σ k).coeff 0| * σ k := add_le_add hs le_rfl
          _ = (∑ a ∈ range M, |(newtonBasis σ k).coeff a|) +
              (|(newtonBasis σ k).coeff 0| +
                ∑ a ∈ range M, |(newtonBasis σ k).coeff (a + 1)|) * σ k := by ring
          _ = (∑ a ∈ range M, |(newtonBasis σ k).coeff a|) +
              (∑ a ∈ range (M + 1), |(newtonBasis σ k).coeff a|) * σ k := by rw [he]
      calc
        ∑ a ∈ range (M + 1), |(newtonBasis σ k * (X - C (σ k))).coeff a|
            ≤ (∑ a ∈ range (M + 1), |(newtonBasis σ k).coeff a|) * (1 + σ k) := by
              have hh : (∑ a ∈ range M, |(newtonBasis σ k).coeff a|) +
                  (∑ a ∈ range (M + 1), |(newtonBasis σ k).coeff a|) * σ k ≤
                  (∑ a ∈ range (M + 1), |(newtonBasis σ k).coeff a|) +
                  (∑ a ∈ range (M + 1), |(newtonBasis σ k).coeff a|) * σ k :=
                add_le_add hshift le_rfl
              simpa only [mul_add, mul_one] using hsum.trans hh

        _ ≤ (∏ j ∈ range k, (1 + σ j)) * (1 + σ k) :=
          mul_le_mul_of_nonneg_right (ih (M + 1)) (by linarith [hσ k])

/-- The generalized Vandermonde bound before replacing each `1+s` by 2. -/
theorem genVandermonde_abs_le_product {p n : ℕ} (s : Fin p → ℝ)
    (hs : ∀ l, s l ∈ Set.Icc (0 : ℝ) 1)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < n) :
    |(Matrix.of fun l i : Fin p => s l ^ E i).det| ≤
      (∏ l : Fin p, (1 + s l)) ^ (n - p) * |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| := by
  classical
  have hpn : p ≤ n := by
    have h := Finset.card_le_card_of_injOn E (s := (univ : Finset (Fin p))) (t := range n)
      (fun i _ => mem_range.mpr (hEn i)) (fun a _ b _ h => hE h)
    simpa using h
  set m := n - p with hm
  have hpm : p + m = n := by omega
  -- the nodes as a sequence and the polynomial `P`
  let σ : ℕ → ℝ := fun k => if h : k < p then s ⟨k, h⟩ else 0
  have hσ : ∀ k, σ k ∈ Set.Icc (0 : ℝ) 1 := by
    intro k
    simp only [σ]
    split_ifs
    · exact hs _
    · exact ⟨le_rfl, zero_le_one⟩
  have hσs : ∀ l : Fin p, σ l.val = s l := by
    intro l
    simp [σ, l.isLt]
  set P : ℝ[X] := newtonBasis σ p with hP
  have hPmonic : P.Monic := by
    rw [hP, newtonBasis]
    exact monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
  have hPdeg : P.natDegree = p := by
    rw [hP, newtonBasis, natDegree_prod_of_monic _ _ fun l _ => monic_X_sub_C _]
    simp
  have hPeval : ∀ l : Fin p, P.eval (s l) = 0 := by
    intro l
    rw [hP, newtonBasis, eval_prod]
    apply prod_eq_zero (mem_range.mpr l.isLt)
    rw [hσs l]
    simp
  have hPne : P ≠ 0 := hPmonic.ne_zero
  -- the exponents and the missing exponents, as a bijection `Fin p ⊕ Fin m ≃ Fin n`
  let Ef : Fin p → Fin n := fun i => ⟨E i, hEn i⟩
  have hEf : Function.Injective Ef := fun a b h => hE (by simpa [Ef] using congrArg Fin.val h)
  let Mset : Finset (Fin n) := (univ.image Ef)ᶜ
  have hMcard : Mset.card = m := by
    rw [card_compl, card_image_of_injective _ hEf]
    simp [hm]
  let kEq : Fin m ≃ Mset := (Mset.equivFinOfCardEq hMcard).symm
  let k : Fin m → Fin n := fun j => (kEq j).val
  have hk : Function.Injective k := fun a b h => kEq.injective (Subtype.ext h)
  have hkE : ∀ j i, k j ≠ Ef i := by
    intro j i h
    have hmem := (kEq j).property
    simp only [Mset, mem_compl, mem_image, mem_univ, true_and, not_exists] at hmem
    exact hmem i h.symm
  let f : Fin p ⊕ Fin m → Fin n := Sum.elim Ef k
  have hf : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [hpm]⟩
    rintro (a | a) (b | b) h
    · exact congrArg Sum.inl (hEf h)
    · exact absurd h.symm (hkE b a)
    · exact absurd h (hkE a b)
    · exact congrArg Sum.inr (hk h)
  let π : Fin p ⊕ Fin m ≃ Fin n := Equiv.ofBijective f hf
  have hπl : ∀ i, π (Sum.inl i) = ⟨E i, hEn i⟩ := fun i => rfl
  have hπr : ∀ j, π (Sum.inr j) = k j := fun j => rfl
  -- the natural order
  let ρ : Fin p ⊕ Fin m ≃ Fin n := finSumFinEquiv.trans (finCongr hpm)
  have hρl : ∀ b : Fin p, ((ρ (Sum.inl b) : Fin n) : ℕ) = b := by
    intro b; simp [ρ]
  have hρr : ∀ i : Fin m, ((ρ (Sum.inr i) : Fin n) : ℕ) = p + i := by
    intro i; simp [ρ]
  -- the two matrices
  set Ω := sharpOmega s k with hΩdef
  set Γ : Matrix (Fin n) (Fin p ⊕ Fin m) ℝ := sharpGamma P with hΓdef
  -- `Ω` after reordering its columns
  have hΩ : Ω.submatrix id π = Matrix.fromBlocks (Matrix.of fun l i : Fin p => s l ^ E i)
      (Matrix.of fun l j => s l ^ (k j : ℕ)) 0 1 := by
    ext (l | j) (i | j')
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.of_apply]
      show Ω (Sum.inl l) (π (Sum.inl i)) = _
      rw [hπl, hΩdef, sharpOmega_inl]
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
      show Ω (Sum.inl l) (π (Sum.inr j')) = _
      rw [hπr, hΩdef, sharpOmega_inl]
    · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      show Ω (Sum.inr j) (π (Sum.inl i)) = _
      rw [hπl, hΩdef, sharpOmega_inr]
      exact if_neg (fun h => hkE j i h.symm)
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      show Ω (Sum.inr j) (π (Sum.inr j')) = _
      rw [hπr, hΩdef, sharpOmega_inr]
      by_cases h : j = j'
      · subst h; simp
      · rw [if_neg (fun h' => h (hk h').symm), if_neg h]
  have hdetΩ : (Ω.submatrix id π).det = (Matrix.of fun l i : Fin p => s l ^ E i).det := by
    rw [hΩ, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]
  -- `Γ` in the natural order is unitriangular
  have hΓρ : Γ.submatrix ρ id = Matrix.fromBlocks 1 (Matrix.of fun b i => (P * X ^ (i : ℕ)).coeff
      ((ρ (Sum.inl b) : Fin n) : ℕ)) 0
      (Matrix.of fun j i : Fin m => (P * X ^ (i : ℕ)).coeff (p + j)) := by
    ext (b | j) (b' | i)
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
      show Γ (ρ (Sum.inl b)) (Sum.inl b') = _
      rw [hΓdef, sharpGamma_inl, hρl]
      by_cases h : b = b'
      · subst h; simp
      · rw [if_neg (fun h' => h (Fin.ext h')), if_neg h]
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.of_apply]
      show Γ (ρ (Sum.inl b)) (Sum.inr i) = _
      rw [hΓdef, sharpGamma_inr]
    · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      show Γ (ρ (Sum.inr j)) (Sum.inl b') = _
      rw [hΓdef, sharpGamma_inl, hρr]
      exact if_neg (by have := b'.isLt; omega)
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
      show Γ (ρ (Sum.inr j)) (Sum.inr i) = _
      rw [hΓdef, sharpGamma_inr, hρr]
  have hΓ22 : (Matrix.of fun j i : Fin m => (P * X ^ (i : ℕ)).coeff (p + j)).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · apply prod_eq_one
      intro i _
      rw [Matrix.of_apply, coeff_mul_X_pow', if_pos (show (i : ℕ) ≤ p + i by omega),
        show p + (i : ℕ) - i = p by omega, ← hPdeg]
      exact hPmonic.coeff_natDegree
    · intro j i hij
      rw [Matrix.of_apply, coeff_mul_X_pow']
      split_ifs with h
      · apply coeff_eq_zero_of_natDegree_lt
        rw [hPdeg]
        have : (i : ℕ) < j := hij
        omega
      · rfl
  have hdetΓ : |(Γ.submatrix π id).det| = 1 := by
    have hτ : Γ.submatrix π id = (Γ.submatrix ρ id).submatrix (π.trans ρ.symm) id := by
      ext a c
      simp only [Matrix.submatrix_apply, id, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [hτ, Matrix.det_permute, hΓρ, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul,
      hΓ22, mul_one]
    rcases Int.units_eq_one_or (Equiv.Perm.sign (π.trans ρ.symm)) with h | h <;> simp [h]
  -- the product `Ω Γ`
  have hprod : (Ω.submatrix id π) * (Γ.submatrix π id) = Ω * Γ :=
    Matrix.submatrix_mul_equiv Ω Γ id π id
  have hΩΓ : Ω * Γ = Matrix.fromBlocks (Matrix.vandermonde s) 0
      (Matrix.of fun j b => if ((k j : Fin n) : ℕ) = (b : ℕ) then (1 : ℝ) else 0)
      (Matrix.of fun j i => (P * X ^ (i : ℕ)).coeff (k j : ℕ)) := by
    ext (l | j) (b | i)
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.mul_apply, Matrix.vandermonde_apply]
      have hb : (b : ℕ) < n := by have := b.isLt; omega
      rw [Finset.sum_eq_single (⟨b, hb⟩ : Fin n)]
      · rw [hΩdef, hΓdef, sharpOmega_inl, sharpGamma_inl, if_pos rfl, mul_one]
      · intro a _ ha
        rw [hΩdef, hΓdef, sharpOmega_inl, sharpGamma_inl, if_neg, mul_zero]
        intro h
        exact ha (Fin.ext h)
      · simp
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.mul_apply, Matrix.zero_apply]
      simp only [hΩdef, hΓdef, sharpOmega_inl, sharpGamma_inr]
      have hdeg : (P * X ^ (i : ℕ)).natDegree < n := by
        rw [natDegree_mul_X_pow _ hPne, hPdeg]
        omega
      have hev := eval_eq_sum_range' hdeg (s l)
      rw [eval_mul, hPeval l, zero_mul] at hev
      have e2 : ∑ a ∈ range n, (P * X ^ (i : ℕ)).coeff a * s l ^ a =
          ∑ a : Fin n, (P * X ^ (i : ℕ)).coeff a * s l ^ (a : ℕ) := Finset.sum_range _
      rw [e2] at hev
      rw [hev]
      apply sum_congr rfl
      intro a _
      ring
    · rw [Matrix.fromBlocks_apply₂₁, Matrix.mul_apply, Matrix.of_apply]
      rw [Finset.sum_eq_single (k j)]
      · rw [hΩdef, hΓdef, sharpOmega_inr, sharpGamma_inl, if_pos rfl, one_mul]
      · intro a _ ha
        rw [hΩdef, sharpOmega_inr, if_neg ha, zero_mul]
      · simp
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.mul_apply, Matrix.of_apply]
      rw [Finset.sum_eq_single (k j)]
      · rw [hΩdef, hΓdef, sharpOmega_inr, sharpGamma_inr, if_pos rfl, one_mul]
      · intro a _ ha
        rw [hΩdef, sharpOmega_inr, if_neg ha, zero_mul]
      · simp
  -- bound for the block `Q`
  set Q : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun j i => (P * X ^ (i : ℕ)).coeff (k j : ℕ) with hQ
  have hQb : |Q.det| ≤ (∏ l : Fin p, (1 + s l)) ^ m := by
    calc |Q.det| ≤ ∏ i, ∑ j, |Q j i| := abs_det_le_prod_col_sum Q
      _ ≤ ∏ _i : Fin m, (∏ l : Fin p, (1 + s l)) := by
          apply prod_le_prod₀ (fun i _ => sum_nonneg fun _ _ => abs_nonneg _)
          intro i _
          have h1 : ∑ j, |Q j i| ≤ ∑ a : Fin n, |(P * X ^ (i : ℕ)).coeff a| := by
            have := Finset.sum_image (s := (univ : Finset (Fin m)))
              (f := fun a : Fin n => |(P * X ^ (i : ℕ)).coeff a|) (fun a _ b _ h => hk h)
            simp only [hQ, Matrix.of_apply]
            rw [← this]
            exact sum_le_sum_of_subset_of_nonneg (subset_univ _)
              (fun _ _ _ => abs_nonneg _)
          have h2 : ∑ a : Fin n, |(P * X ^ (i : ℕ)).coeff a| ≤ ∑ b ∈ range n, |P.coeff b| := by
            have e1 : ∑ a : Fin n, |(P * X ^ (i : ℕ)).coeff a| =
                ∑ a ∈ range n, |(P * X ^ (i : ℕ)).coeff a| :=
              Fin.sum_univ_eq_sum_range (fun a => |(P * X ^ (i : ℕ)).coeff a|) n
            rw [e1]
            have hin : (i : ℕ) ≤ n := by omega
            have hsplit : ∑ a ∈ range n, |(P * X ^ (i : ℕ)).coeff a| =
                ∑ a ∈ Ico (i : ℕ) n, |P.coeff (a - i)| := by
              rw [range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (i : ℕ)) hin,
                Finset.sum_eq_zero, zero_add]
              · apply sum_congr rfl
                intro a ha
                rw [coeff_mul_X_pow', if_pos (mem_Ico.mp ha).1]
              · intro a ha
                rw [coeff_mul_X_pow', if_neg (by simp only [mem_Ico] at ha; omega), abs_zero]
            rw [hsplit, Finset.sum_Ico_eq_sum_range]
            simp only [Nat.add_sub_cancel_left]
            exact sum_le_sum_of_subset_of_nonneg (range_mono (by omega))
              (fun _ _ _ => abs_nonneg _)
          have h3 : ∑ b ∈ range n, |P.coeff b| ≤ ∏ j ∈ range p, (1 + σ j) :=
            newtonBasis_l1_product σ (fun j => (hσ j).1) p n
          have heq : (∏ j ∈ range p, (1 + σ j)) = ∏ l : Fin p, (1 + s l) := by
            rw [Finset.prod_range]
            apply prod_congr rfl
            intro l _
            rw [hσs l]
          rw [heq] at h3
          exact h1.trans (h2.trans h3)
      _ = (∏ l : Fin p, (1 + s l)) ^ m := by rw [prod_const, card_univ, Fintype.card_fin]
  -- assemble
  have hmain : (Matrix.of fun l i : Fin p => s l ^ E i).det * (Γ.submatrix π id).det =
      (∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)) * Q.det := by
    rw [← hdetΩ, ← Matrix.det_mul, hprod, hΩΓ, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_vandermonde]
  have habs := congrArg abs hmain
  rw [abs_mul, abs_mul, hdetΓ, mul_one] at habs
  rw [habs, mul_comm]
  exact mul_le_mul_of_nonneg_right hQb (abs_nonneg _)


end CatalanMeasure
