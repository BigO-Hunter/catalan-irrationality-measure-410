module
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.PCount
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.PBasis
public import Submission.CatalanMeasure.GenD.Uniform.W.Slots.HFam
@[expose] public section
set_option Elab.async false

/-!
# The period family P, design-generic

`perVal P N p s k0 k1 ilo` is the integer bound of Theorem P (with `a = 0`, i.e. `h + h_p < p`):
`(K - |JJ'|)_+ · (Pmax - ilo + 1)` for the polynomials `P` supported in `[ilo, Pmax]`,
`Pmax = min(d + h + h_p - p, η - p)`.  `perVal_le_nullity` proves it is a nullity lower bound.
-/

namespace CatalanMeasure.GenD.Uniform.W.Slots
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin
noncomputable section

/-- `d = h_p - j*`. -/
def perD0 (P : Parameters) (N p : ℕ) (k0 k1 : ℤ) : ℤ := hh p - hpJstar P N p k0 k1

/-- `Pmax = min(d + h + h_p - p, η - p)`. -/
def perPmax (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) : ℤ :=
  min (perD0 P N p k0 k1 + P.h N + hh p - p) ((hpEta P N p s : ℤ) - p)

/-- Digits of the raw columns that see the support of `P`. -/
def perJJ (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) (ilo : ℕ) : Finset ℕ :=
  (Finset.range (P.L N / p + 2)).filter fun J =>
    max (J * p + (hpEta P N p s - p - (perPmax P N p s k0 k1).toNat)) (P.b N) ≤
      min (J * p + (hpEta P N p s - p - ilo)) (P.L N - 1)

/-- Applicability of Theorem P. -/
def perOK (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) (ilo : ℕ) : Prop :=
  P.h N + (p - 1) / 2 < p ∧ s * p + 1 ≤ P.H N ∧ p ≤ hpEta P N p s ∧
    0 ≤ perD0 P N p k0 k1 ∧ (ilo : ℤ) ≤ perPmax P N p s k0 k1 ∧
    hpEta P N p s + 1 ≤ ilo + 2 * p ∧ k0 ≤ k1

instance (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) (ilo : ℕ) :
    Decidable (perOK P N p s k0 k1 ilo) := by
  unfold perOK; infer_instance

/-- **Theorem P, integer value.** -/
def perVal (P : Parameters) (N p s : ℕ) (k0 k1 : ℤ) (ilo : ℕ) : ℕ :=
  if perOK P N p s k0 k1 ilo then
    (hpK k0 k1 - (perJJ P N p s k0 k1 ilo).card) * ((perPmax P N p s k0 k1).toNat - ilo + 1)
  else 0

variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `U`-slot relation: `Σ_t s_t lam_t = (X-1)^{h+h_p} Σ_t s_t g_t`. -/
theorem lam_combination (hp2 : p ≠ 2) {D : ℕ} (sc : Fin D → ZMod p) :
    ∑ t : Fin D, C (sc t) * hLam P N p t =
      (X - 1) ^ (P.h N + (p - 1) / 2) * ∑ t : Fin D, C (sc t) * gBasis p t := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold hLam
  rw [f_eq_gBasis hp2, pow_add]
  ring

theorem perVal_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (s : ℕ) (k0 k1 : ℤ) (ilo : ℕ) : perVal P N p s k0 k1 ilo ≤ nullity P N p := by
  classical
  unfold perVal
  split_ifs with hc
  swap
  · exact Nat.zero_le _
  obtain ⟨hv, hs, hpe, hd0, hilo1, hilo2, hk⟩ := hc
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hpe' := p_eq_hh hp2
  have hjs : 1 ≤ hpJstar P N p k0 k1 := le_max_left _ _
  have hjs2 : -(P.g N : ℤ) - k0 * p ≤ hpJstar P N p k0 k1 :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hjs3 : (k1 + 1) * (p : ℤ) - ((P.n N : ℤ) - 1 - P.g N) ≤ hpJstar P N p k0 k1 :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hPm1 : perPmax P N p s k0 k1 ≤ perD0 P N p k0 k1 + P.h N + hh p - p := min_le_left _ _
  have hPm2 : perPmax P N p s k0 k1 ≤ (hpEta P N p s : ℤ) - p := min_le_right _ _
  have hhh : hh p = (((p - 1) / 2 : ℕ) : ℤ) := rfl
  set Dn : ℕ := (perD0 P N p k0 k1).toNat + 1 with hDn
  have hDz : (Dn : ℤ) = perD0 P N p k0 k1 + 1 := by
    rw [hDn]; push_cast; rw [Int.toNat_of_nonneg hd0]
  have hKe : ((hpK k0 k1 : ℕ) : ℤ) = k1 - k0 + 1 := by
    unfold hpK; rw [Int.toNat_of_nonneg (by omega)]
  have hDhp : Dn ≤ (p - 1) / 2 := by
    have : (Dn : ℤ) ≤ hh p := by unfold perD0 at hDz; omega
    omega
  have hvirt : hVirt P N p (hpK k0 k1) Dn k0 = 0 := by
    refine hVirt_zero k0 (hpJstar P N p k0 k1) hp2 hjs hjs2 ?_ (by unfold perD0 at hDz; omega)
    have : ((k0 + (hpK k0 k1 : ℕ) : ℤ)) = k1 + 1 := by rw [hKe]; ring
    rw [this]; exact sub_le_comm.mp hjs3
  have hdomAll : ∀ x, x ∈ (hSystem P N p hp2 (hpK k0 k1) Dn k0 hDhp).dom := by
    intro x
    have hb : hBad P N p (hpK k0 k1) Dn k0 = ∅ := Finset.card_eq_zero.mp hvirt
    exact (mem_badDom (hBad P N p (hpK k0 k1) Dn k0) x).mpr (fun b hb' => by rw [hb] at hb'; simp at hb')
  -- polynomial data
  set Pm : ℕ := (perPmax P N p s k0 k1).toNat with hPm
  have hPmz : (Pm : ℤ) = perPmax P N p s k0 k1 := by
    rw [hPm]; exact Int.toNat_of_nonneg (by omega)
  set m : ℕ := Pm - ilo + 1 with hm
  have hmle : ∀ i : Fin m, ilo + (i : ℕ) ≤ Pm := fun i => by have := i.isLt; omega
  set c0 : ℕ := p - (P.h N + (p - 1) / 2) with hc0
  have hexist : ∀ i : Fin m, ∃ sc : Fin Dn → ZMod p,
      (X - 1 : (ZMod p)[X]) ^ c0 * X ^ (ilo + (i : ℕ)) = ∑ t : Fin Dn, C (sc t) * gBasis p t := by
    intro i
    refine exists_combination hp2 Dn hDhp _ ?_
    have hdeg : ((X - 1 : (ZMod p)[X]) ^ c0 * X ^ (ilo + (i : ℕ))).natDegree = c0 + (ilo + i) := by
      have h1 : (X - 1 : (ZMod p)[X]).natDegree = 1 := by compute_degree!
      rw [natDegree_mul (pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1 : ZMod p)))
        (pow_ne_zero _ X_ne_zero), natDegree_pow, h1, natDegree_X_pow]; ring
    have hne : ((X - 1 : (ZMod p)[X]) ^ c0 * X ^ (ilo + (i : ℕ))) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by simpa using X_sub_C_ne_zero (1 : ZMod p)))
        (pow_ne_zero _ X_ne_zero)
    rw [degree_eq_natDegree hne, hdeg]
    have : c0 + (ilo + (i : ℕ)) < Dn := by
      have := hmle i
      have h2 : (Dn : ℤ) = perD0 P N p k0 k1 + 1 := hDz
      have : ((c0 + (ilo + (i : ℕ)) : ℕ) : ℤ) < Dn := by
        push_cast [hc0]
        rw [Nat.cast_sub (by omega : P.h N + (p - 1) / 2 ≤ p)]
        push_cast; omega
      exact_mod_cast this
    exact_mod_cast this
  choose sc hsc using hexist
  have hrel : ∀ i : Fin m, ∑ t : Fin Dn, C (sc i t) * (hSystem P N p hp2 (hpK k0 k1) Dn k0 hDhp).lam t =
      X ^ p * (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]) - X ^ (ilo + (i : ℕ)) := by
    intro i
    show ∑ t : Fin Dn, C (sc i t) * hLam P N p t = _
    rw [lam_combination hp2, ← hsc i, ← mul_assoc, ← pow_add]
    have : P.h N + (p - 1) / 2 + c0 = p := by rw [hc0]; omega
    rw [this, sub_one_pow_prime]; ring
  have hind : ∀ cc : Fin m → ZMod p,
      ∑ i, C (cc i) * (X ^ p * (X ^ (ilo + (i : ℕ)) : (ZMod p)[X]) - X ^ (ilo + (i : ℕ))) = 0 →
        cc = 0 := by
    intro cc hcc
    have h1 : (X ^ p - 1 : (ZMod p)[X]) * X ^ ilo * ∑ i : Fin m, C (cc i) * X ^ (i : ℕ) = 0 := by
      rw [← hcc, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_add]; ring
    have hne : (X ^ p - 1 : (ZMod p)[X]) * X ^ ilo ≠ 0 :=
      mul_ne_zero (by simpa using X_pow_sub_C_ne_zero hp0 (1 : ZMod p)) (pow_ne_zero _ X_ne_zero)
    have h2 : ∑ i : Fin m, C (cc i) * X ^ (i : ℕ) = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd h hne
      · exact h
    funext i
    have := congrArg (fun q => q.coeff (i : ℕ)) h2
    simpa [finset_sum_coeff, coeff_C_mul, coeff_X_pow, Fin.val_inj] using this
  -- the kernel of the difference covectors
  obtain ⟨V, hV1, hV2⟩ := exists_common_kernel (K := hpK k0 k1) (perJJ P N p s k0 k1 ilo)
    (fun J => (hSystem P N p hp2 (hpK k0 k1) Dn k0 hDhp).prof.psi (P.H N) J s -
      (hSystem P N p hp2 (hpK k0 k1) Dn k0 hDhp).prof.psi (P.H N) J ((s : ℤ) + 1))
  have hetaz : (P.H N : ℤ) - 1 - (hpEta P N p s : ℤ) = s * p := by
    unfold hpEta; omega
  have hPmax : Pm + p ≤ hpEta P N p s := by
    have : (Pm : ℤ) + p ≤ hpEta P N p s := by rw [hPmz]; omega
    exact_mod_cast this
  have hper := (hSystem P N p hp2 (hpK k0 k1) Dn k0 hDhp).period_nullity hP hN hp2 hH
    (m := m) V hdomAll (eta := hpEta P N p s) (s := s) (ilo := ilo) (Pmax := Pm) hetaz hPmax
    hilo2 (fun i => X ^ (ilo + (i : ℕ))) (fun i => by rw [natDegree_X_pow]; exact hmle i)
    (fun i e he => by rw [coeff_X_pow, if_neg (by omega)]) sc hrel hind
    (fun j h1 h2 hc hl hr y hy => by
      have hJ : j / p ∈ perJJ P N p s k0 k1 ilo := by
        unfold perJJ
        rw [Finset.mem_filter, Finset.mem_range]
        have hL : j / p ≤ P.L N / p := Nat.div_le_div_right h2.le
        have hjd := Nat.div_add_mod j p
        have e2 : j / p * p + j % p = j := by rw [mul_comm]; exact hjd
        refine ⟨by omega, ?_⟩
        simp only [max_le_iff, le_min_iff]
        have hPm' : Pm = (perPmax P N p s k0 k1).toNat := rfl
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega
      have := hV2 (j / p) hJ y hy
      exact sub_eq_zero.mp this)
  have hmul : (hpK k0 k1 - (perJJ P N p s k0 k1 ilo).card) * m ≤ m * finrank (ZMod p) V := by
    rw [mul_comm]; exact Nat.mul_le_mul_left _ hV1
  exact hmul.trans hper

#print axioms perVal_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.Slots
