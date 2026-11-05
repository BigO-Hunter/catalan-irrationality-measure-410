module

public import Submission.CatalanMeasure.GenVandermonde
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.Logic.Equiv.Fin.Basic

@[expose] public section

/-!
# A sharper generalized Vandermonde bound

For nodes `s₀, …, s_{p-1} ∈ [0, 1]` and distinct exponents `E₀, …, E_{p-1} < n`,

  `|det [s_l ^ E_i]| ≤ 2 ^ (p (n - p)) · |∏_{i<j} (s_j - s_i)|`.

Proof.  Let `m = n - p`, let `k₀, …, k_{m-1}` enumerate the exponents below `n` that are not
among the `E_i`, and let `P = ∏_l (X - s_l)`.  Consider two `n × n` matrices:

* `Ω`, whose rows are the evaluations at the `s_l` and the coefficient functionals `[X^{k_j}]`,
  applied to the monomials `X^a`, `a < n`;
* `Γ`, whose columns are the coefficient vectors of `X^b` (`b < p`) and of `P X^i` (`i < m`).

After reordering columns, `Ω` is block triangular with diagonal blocks `[s_l ^ E_i]` and the
identity, so `|det Ω| = |det [s_l ^ E_i]|`.  `Γ` is unitriangular up to a permutation, so
`|det Γ| = 1`.  Since `P` vanishes at every node, `Ω Γ` is block triangular with diagonal
blocks the Vandermonde matrix of `s` and `Q = [(P X^i)_{k_j}]`.  Each column of `Q` has
`ℓ¹` norm at most `∏ (1 + s_l) ≤ 2^p`.
-/

open Polynomial Finset Matrix

namespace CatalanMeasure

/-- Rows: evaluation at the nodes, then the coefficient functionals `[X^{k j}]`;
columns: the monomials `X^a`, `a < n`. -/
noncomputable def sharpOmega {p m n : ℕ} (s : Fin p → ℝ) (k : Fin m → Fin n) :
    Matrix (Fin p ⊕ Fin m) (Fin n) ℝ :=
  Matrix.of fun r a => Sum.elim (fun l => s l ^ (a : ℕ)) (fun j => if a = k j then (1 : ℝ) else 0) r

/-- Columns: the coefficient vectors of `X^b` (`b < p`) and of `P X^i` (`i < m`). -/
noncomputable def sharpGamma {p m n : ℕ} (P : ℝ[X]) : Matrix (Fin n) (Fin p ⊕ Fin m) ℝ :=
  Matrix.of fun a c => Sum.elim (fun b : Fin p => if (a : ℕ) = b then (1 : ℝ) else 0)
    (fun i : Fin m => (P * X ^ (i : ℕ)).coeff a) c

@[simp] theorem sharpOmega_inl {p m n : ℕ} (s : Fin p → ℝ) (k : Fin m → Fin n) (l : Fin p)
    (a : Fin n) : sharpOmega s k (Sum.inl l) a = s l ^ (a : ℕ) := rfl

@[simp] theorem sharpOmega_inr {p m n : ℕ} (s : Fin p → ℝ) (k : Fin m → Fin n) (j : Fin m)
    (a : Fin n) : sharpOmega s k (Sum.inr j) a = if a = k j then 1 else 0 := rfl

@[simp] theorem sharpGamma_inl {p m n : ℕ} (P : ℝ[X]) (a : Fin n) (b : Fin p) :
    sharpGamma (m := m) P a (Sum.inl b) = if (a : ℕ) = b then 1 else 0 := rfl

@[simp] theorem sharpGamma_inr {p m n : ℕ} (P : ℝ[X]) (a : Fin n) (i : Fin m) :
    sharpGamma (p := p) P a (Sum.inr i) = (P * X ^ (i : ℕ)).coeff a := rfl

/-- **Sharper generalized Vandermonde bound.** -/
theorem genVandermonde_abs_le_two {p n : ℕ} (s : Fin p → ℝ)
    (hs : ∀ l, s l ∈ Set.Icc (0 : ℝ) 1)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < n) :
    |(Matrix.of fun l i : Fin p => s l ^ E i).det| ≤
      (2 : ℝ) ^ (p * (n - p)) * |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| := by
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
  have hQb : |Q.det| ≤ (2 : ℝ) ^ (p * m) := by
    calc |Q.det| ≤ ∏ i, ∑ j, |Q j i| := abs_det_le_prod_col_sum Q
      _ ≤ ∏ _i : Fin m, (2 : ℝ) ^ p := by
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
          have h3 : ∑ b ∈ range n, |P.coeff b| ≤ (2 : ℝ) ^ p := newtonBasis_l1 σ hσ p n
          linarith
      _ = (2 : ℝ) ^ (p * m) := by rw [prod_const, card_univ, Fintype.card_fin, ← pow_mul]
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
