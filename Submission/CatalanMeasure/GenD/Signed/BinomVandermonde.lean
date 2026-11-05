module

public import Submission.CatalanMeasure.GenVandermondeSharp
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

@[expose] public section

/-!
# Binomial generalized Vandermonde bound (Lemma V)

For nodes `s₀, …, s_{p-1} ∈ [0, 1]`, distinct exponents `E_i < n`, `m = n - p`, and
`K = {0, …, n-1} \ E = {k₁, …, k_m}`,

  `|det [s_l ^ E_i]| ≤ ∏_{k ∈ K} β(k) · |∏_{i<j} (s_j - s_i)|`,
  `β(k) = ∑_{i<m} C(p, p - k + i)`  (`C(p, r) = 0` outside `[0, p]`).

The proof reuses the `Ω`–`Γ` factorisation of `genVandermonde_abs_le_two`
(`|det [s^E]| = |V(s)| · |det Q|`, `Q_{j,i} = [X^{k_j - i}] P`), but applies Hadamard's inequality
to the *rows* of `Q`: row `j` has `ℓ¹` norm `∑_i |[X^{k_j - i}] P| ≤ ∑_i C(p, k_j - i) = β(k_j)`.
-/

open Polynomial Finset Matrix

namespace CatalanMeasure

/-- Term `i` of `β(k)`: `C(p, p - k + i)`, read as `0` unless `0 ≤ p - k + i ≤ p`. -/
def binomBetaTerm (p k i : ℕ) : ℕ := if k ≤ p + i then p.choose (p + i - k) else 0

/-- `β(k) = ∑_{i<m} C(p, p - k + i)` of Lemma V. -/
def binomBeta (p m k : ℕ) : ℕ := ∑ i ∈ range m, binomBetaTerm p k i

theorem binomBetaTerm_le_two_pow (p k i : ℕ) :
    binomBetaTerm p k i ≤ 2 ^ p := by
  unfold binomBetaTerm
  split_ifs
  · exact Nat.choose_le_two_pow p _
  · exact Nat.zero_le _

/-- Row bound: the entries of row `kk` of `Q = [X^{kk}](P X^i)` are bounded by the terms of `β`. -/
theorem abs_coeff_mul_X_pow_le_binomBetaTerm {p : ℕ} (P : ℝ[X])
    (hP : ∀ a, |P.coeff a| ≤ (p.choose a : ℝ)) (i kk : ℕ) :
    |(P * X ^ i).coeff kk| ≤ (binomBetaTerm p kk i : ℝ) := by
  rw [coeff_mul_X_pow']
  by_cases hik : i ≤ kk
  · rw [if_pos hik]
    refine (hP _).trans ?_
    unfold binomBetaTerm
    by_cases hk : kk ≤ p + i
    · rw [if_pos hk]
      have : p.choose (kk - i) = p.choose (p + i - kk) := by
        rw [← Nat.choose_symm (show kk - i ≤ p by omega)]
        congr 1
        omega
      rw [this]
    · rw [if_neg hk, Nat.choose_eq_zero_of_lt (by omega)]
  · rw [if_neg hik, abs_zero]
    exact Nat.cast_nonneg _

/-- **Lemma V (binomial generalized Vandermonde).** -/
theorem genVandermonde_abs_le_binom {p n : ℕ} (s : Fin p → ℝ)
    (hs : ∀ l, s l ∈ Set.Icc (0 : ℝ) 1)
    (E : Fin p → ℕ) (hE : Function.Injective E) (hEn : ∀ i, E i < n) :
    |(Matrix.of fun l i : Fin p => s l ^ E i).det| ≤
      (∏ k ∈ range n \ univ.image E, (binomBeta p (n - p) k : ℝ)) *
        |∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)| := by
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
  -- bound for the block `Q`, by rows
  set Q : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun j i => (P * X ^ (i : ℕ)).coeff (k j : ℕ) with hQ
  have hPb : ∀ a, |P.coeff a| ≤ (p.choose a : ℝ) := (newtonBasis_bounds σ hσ p).2
  have hQb : |Q.det| ≤ ∏ j : Fin m, (binomBeta p m (k j : ℕ) : ℝ) := by
    calc |Q.det| = |Q.transpose.det| := by rw [Matrix.det_transpose]
      _ ≤ ∏ j, ∑ i, |Q.transpose i j| := abs_det_le_prod_col_sum Q.transpose
      _ ≤ ∏ j : Fin m, (binomBeta p m (k j : ℕ) : ℝ) := by
          apply prod_le_prod₀ (fun j _ => sum_nonneg fun _ _ => abs_nonneg _)
          intro j _
          have e1 : ∑ i : Fin m, |Q.transpose i j| =
              ∑ i ∈ range m, |(P * X ^ i).coeff (k j : ℕ)| :=
            Fin.sum_univ_eq_sum_range (fun i => |(P * X ^ i).coeff (k j : ℕ)|) m
          rw [e1]
          unfold binomBeta
          push_cast
          exact sum_le_sum fun i _ => abs_coeff_mul_X_pow_le_binomBetaTerm P hPb i _
  -- reindex the product over `K`
  have hK : (range n \ univ.image E) = Mset.map Fin.valEmbedding := by
    ext x
    simp only [mem_sdiff, mem_range, mem_image, mem_univ, true_and, mem_map, Fin.valEmbedding_apply,
      Mset, mem_compl, not_exists]
    constructor
    · rintro ⟨hx, hx2⟩
      exact ⟨⟨x, hx⟩, fun i h => hx2 i (by simpa [Ef] using congrArg Fin.val h), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.isLt, fun i h => ha i (Fin.ext (by simpa [Ef] using h))⟩
  have hprodK : ∏ k' ∈ range n \ univ.image E, (binomBeta p m k' : ℝ) =
      ∏ j : Fin m, (binomBeta p m (k j : ℕ) : ℝ) := by
    rw [hK, Finset.prod_map]
    simp only [Fin.valEmbedding_apply]
    rw [← Finset.prod_coe_sort Mset (fun a : Fin n => (binomBeta p m (a : ℕ) : ℝ))]
    exact (Equiv.prod_comp kEq (fun b : Mset => (binomBeta p m ((b : Fin n) : ℕ) : ℝ))).symm
  -- assemble
  have hmain : (Matrix.of fun l i : Fin p => s l ^ E i).det * (Γ.submatrix π id).det =
      (∏ i : Fin p, ∏ j ∈ Ioi i, (s j - s i)) * Q.det := by
    rw [← hdetΩ, ← Matrix.det_mul, hprod, hΩΓ, Matrix.det_fromBlocks_zero₁₂,
      Matrix.det_vandermonde]
  have habs := congrArg abs hmain
  rw [abs_mul, abs_mul, hdetΓ, mul_one] at habs
  rw [habs, mul_comm, hprodK]
  exact mul_le_mul_of_nonneg_right hQb (abs_nonneg _)

/-! ### Consequences of Lemma V -/

/-- `β(k) ≤ m · 2^p`. -/
theorem binomBeta_le_mul_two_pow (p m k : ℕ) : binomBeta p m k ≤ m * 2 ^ p := by
  unfold binomBeta
  calc ∑ i ∈ range m, binomBetaTerm p k i ≤ ∑ _i ∈ range m, 2 ^ p :=
        sum_le_sum fun i _ => binomBetaTerm_le_two_pow p k i
    _ = m * 2 ^ p := by simp

/-- Sharper: `β(k) ≤ 2^p` (the terms are distinct binomial coefficients of `p`). -/
theorem binomBeta_le_two_pow (p m k : ℕ) : binomBeta p m k ≤ 2 ^ p := by
  unfold binomBeta
  have h1 : ∑ i ∈ range m, binomBetaTerm p k i =
      ∑ i ∈ (range m).filter (fun i => k ≤ p + i), p.choose (p + i - k) := by
    rw [Finset.sum_filter]
    refine sum_congr rfl fun i _ => ?_
    unfold binomBetaTerm
    rfl
  rw [h1]
  have hinj : Set.InjOn (fun i => p + i - k) ((range m).filter (fun i => k ≤ p + i) : Finset ℕ) := by
    intro a ha b hb h
    simp only [coe_filter, Set.mem_setOf_eq, mem_range] at ha hb h
    omega
  rw [← Finset.sum_image (f := fun a => p.choose a) hinj]
  calc ∑ a ∈ ((range m).filter (fun i => k ≤ p + i)).image (fun i => p + i - k), p.choose a
      = ∑ a ∈ (((range m).filter (fun i => k ≤ p + i)).image (fun i => p + i - k)).filter
          (· ≤ p), p.choose a := by
        symm
        apply Finset.sum_filter_of_ne
        intro a _ ha
        by_contra h
        exact ha (Nat.choose_eq_zero_of_lt (by omega))
    _ ≤ ∑ a ∈ range (p + 1), p.choose a := by
        apply Finset.sum_le_sum_of_subset
        intro a ha
        simp only [mem_filter] at ha
        exact mem_range.mpr (by omega)
    _ = 2 ^ p := Nat.sum_range_choose p

/-- `log β(k) ≤ p log 2 + log m` (for `m ≥ 1`). -/
theorem log_binomBeta_le (p m k : ℕ) (hm : 1 ≤ m) :
    Real.log (binomBeta p m k) ≤ p * Real.log 2 + Real.log m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  rcases Nat.eq_zero_or_pos (binomBeta p m k) with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
    have : 0 ≤ (p : ℝ) * Real.log 2 := by positivity
    linarith
  · have hb : (binomBeta p m k : ℝ) ≤ m * 2 ^ p := by exact_mod_cast binomBeta_le_mul_two_pow p m k
    calc Real.log (binomBeta p m k) ≤ Real.log (m * 2 ^ p) :=
          Real.log_le_log (by exact_mod_cast hpos) hb
      _ = p * Real.log 2 + Real.log m := by
          rw [Real.log_mul hm'.ne' (by positivity), Real.log_pow]; ring

/-- Sharper: `log β(k) ≤ p log 2`. -/
theorem log_binomBeta_le_of_two_pow (p m k : ℕ) :
    Real.log (binomBeta p m k) ≤ p * Real.log 2 := by
  rcases Nat.eq_zero_or_pos (binomBeta p m k) with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
    positivity
  · have hb : (binomBeta p m k : ℝ) ≤ 2 ^ p := by exact_mod_cast binomBeta_le_two_pow p m k
    calc Real.log (binomBeta p m k) ≤ Real.log (2 ^ p) :=
          Real.log_le_log (by exact_mod_cast hpos) hb
      _ = p * Real.log 2 := by rw [Real.log_pow]

/-- The window maximum `max_{r ∈ [n-m-k, n-1-k]} C(n, r)` (negative `r` contribute `0`). -/
def binomWindowMax (n m k : ℕ) : ℕ :=
  ((Finset.Icc ((n : ℤ) - m - k) ((n : ℤ) - 1 - k)).filter (fun r : ℤ => 0 ≤ r)).sup
    fun r => n.choose r.toNat

/-- `β(k) ≤ m · max_{r ∈ [n-m-k, n-1-k]} C(n, r)`, where `p = n - m`. -/
theorem binomBeta_le_mul_window (p m n k : ℕ) (hpm : p + m = n) :
    binomBeta p m k ≤ m * binomWindowMax n m k := by
  unfold binomBeta
  calc ∑ i ∈ range m, binomBetaTerm p k i ≤ ∑ _i ∈ range m, binomWindowMax n m k := by
        refine sum_le_sum fun i hi => ?_
        have hi' := mem_range.mp hi
        unfold binomBetaTerm
        split_ifs with hk
        · refine le_trans (Nat.choose_le_choose (p + i - k) (show p ≤ n by omega)) ?_
          unfold binomWindowMax
          have hmem : ((p + i - k : ℕ) : ℤ) ∈ (Finset.Icc ((n : ℤ) - m - k)
              ((n : ℤ) - 1 - k)).filter (fun r : ℤ => 0 ≤ r) := by
            simp only [mem_filter, mem_Icc]
            refine ⟨⟨?_, ?_⟩, Int.natCast_nonneg _⟩ <;> omega
          have := Finset.le_sup (f := fun r : ℤ => n.choose r.toNat) hmem
          simpa using this
        · exact Nat.zero_le _
    _ = m * binomWindowMax n m k := by simp

/-- The entropy bound for a single binomial coefficient: `log C(n, j) ≤ n H(j/n)`. -/
theorem log_choose_le_mul_binEntropy (n j : ℕ) (hj : j ≤ n) :
    Real.log (n.choose j) ≤ n * Real.binEntropy ((j : ℝ) / n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : j = 0 := by omega
    subst this
    simp
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  rcases hj.eq_or_lt with rfl | hjn
  · simp [Real.binEntropy_one, div_self (show (j : ℝ) ≠ 0 by exact_mod_cast hj0.ne')]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hjR : (0 : ℝ) < j := by exact_mod_cast hj0
  have hjnR : (j : ℝ) < n := by exact_mod_cast hjn
  set x : ℝ := (j : ℝ) / n with hx
  have hx0 : 0 < x := div_pos hjR hn'
  have hx1 : x < 1 := (div_lt_one hn').mpr hjnR
  have hy0 : 0 < 1 - x := by linarith
  -- `C(n,j) x^j (1-x)^(n-j) ≤ (x + (1-x))^n = 1`
  have key : (n.choose j : ℝ) * (x ^ j * (1 - x) ^ (n - j)) ≤ 1 := by
    have h := add_pow x (1 - x) n
    rw [show x + (1 - x) = 1 by ring, one_pow] at h
    have hle := Finset.single_le_sum (f := fun i => x ^ i * (1 - x) ^ (n - i) * (n.choose i : ℝ))
      (fun i _ => by positivity) (mem_range.mpr (Nat.lt_succ_of_le hj))
    calc (n.choose j : ℝ) * (x ^ j * (1 - x) ^ (n - j))
        = x ^ j * (1 - x) ^ (n - j) * (n.choose j : ℝ) := by ring
      _ ≤ _ := hle
      _ = 1 := h.symm
  have hpos : 0 < (n.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hj
  have hlog := Real.log_le_log (by positivity) key
  rw [Real.log_one, Real.log_mul hpos.ne' (by positivity), Real.log_mul (by positivity)
    (by positivity), Real.log_pow, Real.log_pow] at hlog
  have hnj : ((n - j : ℕ) : ℝ) = n - j := by rw [Nat.cast_sub hj]
  rw [hnj] at hlog
  have h1 : (n : ℝ) * x = j := by rw [hx]; field_simp
  have h2 : (n : ℝ) * (1 - x) = n - j := by rw [mul_sub, h1]; ring
  have hdef : Real.binEntropy x = x * -Real.log x + (1 - x) * -Real.log (1 - x) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    simp only [Real.negMulLog]
    ring
  rw [hdef]
  have : (n : ℝ) * (x * -Real.log x + (1 - x) * -Real.log (1 - x)) =
      -((n : ℝ) * x) * Real.log x - ((n : ℝ) * (1 - x)) * Real.log (1 - x) := by ring
  rw [this, h1, h2]
  linarith

/-- `C(n, r) ≤ C(n, j)` for `r ≤ j ≤ n/2`. -/
theorem choose_le_choose_of_le_half {n r j : ℕ} (hrj : r ≤ j) (hj : j ≤ n / 2) :
    n.choose r ≤ n.choose j := by
  induction j, hrj using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- **Entropy form** (`k/n ≥ 1/2`): `log β(k) ≤ log m + n H(k/n)`, `H` the binary entropy. -/
theorem log_binomBeta_le_entropy (p m n k : ℕ) (hpm : p + m = n) (hm : 1 ≤ m) (hkn : k < n)
    (hhalf : n ≤ 2 * k) :
    Real.log (binomBeta p m k) ≤ Real.log m + n * Real.binEntropy ((k : ℝ) / n) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hent : 0 ≤ (n : ℝ) * Real.binEntropy ((k : ℝ) / n) := by
    apply mul_nonneg hn.le
    apply Real.binEntropy_nonneg (div_nonneg (Nat.cast_nonneg _) hn.le)
    exact (div_le_one hn).mpr (by exact_mod_cast hkn.le)
  have hlm : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
  set j := n - 1 - k with hj
  have hjn : j ≤ n := by omega
  have hjhalf : j ≤ n / 2 := by omega
  -- every term is at most `C(n, j)`
  have hterm : ∀ i ∈ range m, binomBetaTerm p k i ≤ n.choose j := by
    intro i hi
    have hi' := mem_range.mp hi
    unfold binomBetaTerm
    split_ifs with hk
    · exact (Nat.choose_le_choose (p + i - k) (show p ≤ n by omega)).trans
        (choose_le_choose_of_le_half (by omega) hjhalf)
    · exact Nat.zero_le _
  have hB : binomBeta p m k ≤ m * n.choose j := by
    unfold binomBeta
    calc ∑ i ∈ range m, binomBetaTerm p k i ≤ ∑ _i ∈ range m, n.choose j := sum_le_sum hterm
      _ = m * n.choose j := by simp
  have hH : Real.binEntropy ((j : ℝ) / n) ≤ Real.binEntropy ((k : ℝ) / n) := by
    have e : (j : ℝ) / n = 1 - ((k : ℝ) + 1) / n := by
      rw [hj, Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; field_simp; ring
    rw [e, Real.binEntropy_one_sub]
    have hnk : (n : ℝ) ≤ 2 * k := by exact_mod_cast hhalf
    have hkn' : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have ha : (k : ℝ) / n ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
      refine ⟨?_, (div_le_one hn).mpr (by linarith)⟩
      rw [le_div_iff₀ hn]; linarith
    have hb : ((k : ℝ) + 1) / n ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
      refine ⟨?_, (div_le_one hn).mpr hkn'⟩
      rw [le_div_iff₀ hn]; linarith
    exact Real.binEntropy_strictAntiOn.antitoneOn ha hb
      (div_le_div_of_nonneg_right (by linarith) hn.le)
  rcases Nat.eq_zero_or_pos (binomBeta p m k) with h0 | hpos
  · rw [h0]; simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · have hb : (binomBeta p m k : ℝ) ≤ m * n.choose j := by exact_mod_cast hB
    have hcpos : 0 < (n.choose j : ℝ) := by exact_mod_cast Nat.choose_pos hjn
    calc Real.log (binomBeta p m k) ≤ Real.log (m * n.choose j) :=
          Real.log_le_log (by exact_mod_cast hpos) hb
      _ = Real.log m + Real.log (n.choose j) := Real.log_mul hm'.ne' hcpos.ne'
      _ ≤ Real.log m + n * Real.binEntropy ((j : ℝ) / n) := by
          gcongr; exact log_choose_le_mul_binEntropy n j hjn
      _ ≤ Real.log m + n * Real.binEntropy ((k : ℝ) / n) := by gcongr

#print axioms genVandermonde_abs_le_binom
#print axioms binomBeta_le_two_pow
#print axioms log_binomBeta_le
#print axioms binomBeta_le_mul_window
#print axioms log_binomBeta_le_entropy

end CatalanMeasure
