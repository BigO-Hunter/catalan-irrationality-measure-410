module
public import Submission.CatalanMeasure.Parametric.RawDigitReduction
@[expose] public section
namespace CatalanMeasure.Parametric
open Polynomial
open OAI.InternalCatalan
open scoped BigOperators
noncomputable section
theorem filterBinomial_prime_digit (P : Parameters) {p v : ℕ} [hp : Fact p.Prime] :
    ((P.q0 * p).choose v : ZMod p) =
      if v % p = 0 then (P.q0.choose (v / p) : ZMod p) else 0 := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := p) (n := P.q0 * p) (k := v)
  have hc := (ZMod.natCast_eq_natCast_iff _ _ p).mpr h
  rw [Nat.mul_mod_left, Nat.mul_div_cancel P.q0 hp.out.pos, Nat.cast_mul] at hc
  by_cases hv : v % p = 0
  · simpa [hv] using hc
  · have hzero : (0 : ℕ).choose (v % p) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    simpa [hv, hzero] using hc

theorem filterCoeffRat_prime_digit_reduction (P : Parameters) {p v : ℕ} [hp : Fact p.Prime] :
    ((filterCoeffRat P p v).den : ZMod p) ≠ 0 ∧
      ((filterCoeffRat P p v).num : ZMod p) / ((filterCoeffRat P p v).den : ZMod p) =
        if v % p = 0 then
          (-1 : ZMod p) ^ (v / p) * (P.q0.choose (v / p) : ZMod p) else 0 := by
  have hcanon := And.intro (filterCoeff_den P (p := p) p v) (filterCoeff_residue P p p v)
  refine ⟨hcanon.1, ?_⟩
  change palindromicRatResidue p (filterCoeffRat P p v) = _
  rw [hcanon.2, Parameters.q, filterBinomial_prime_digit P]
  by_cases hv : v % p = 0
  · have hfactor : v = p * (v / p) := by
      have h := Nat.mod_add_div v p
      rw [hv, zero_add] at h
      exact h.symm
    have hsign : (-1 : ZMod p) ^ v = (-1 : ZMod p) ^ (v / p) := by
      calc
        (-1 : ZMod p) ^ v = (-1 : ZMod p) ^ (p * (v / p)) :=
          congrArg (fun n : ℕ => (-1 : ZMod p) ^ n) hfactor
        _ = ((-1 : ZMod p) ^ p) ^ (v / p) := pow_mul _ _ _
        _ = _ := by rw [ZMod.pow_card]
    rw [ite_eq_left hv, ite_eq_left hv, hsign]
  · rw [ite_eq_right hv, ite_eq_right hv, mul_zero]

theorem filteredEntry_scaled_residue_sum (P : Parameters) {p r k : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hpH : P.H 1 < p) (hk : k < P.n p) (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * filteredEntryRat P z p r k).den : ZMod p) ≠ 0 ∧
      (((p : ℚ) ^ 2 * filteredEntryRat P z p r k).num : ZMod p) /
        (((p : ℚ) ^ 2 * filteredEntryRat P z p r k).den : ZMod p) =
          ∑ v ∈ Finset.range (P.q p + 1),
            (((filterCoeffRat P p v).num : ZMod p) / ((filterCoeffRat P p v).den : ZMod p)) *
              ((((p : ℚ) ^ 2 * rawEntryRat P z p r (P.b p + k + v)).num : ZMod p) /
                (((p : ℚ) ^ 2 * rawEntryRat P z p r (P.b p + k + v)).den : ZMod p)) := by
  let R : ℚ → ZMod p := fun x => (x.num : ZMod p) / (x.den : ZMod p)
  let f : ℕ → ℚ := fun v =>
    filterCoeffRat P p v * ((p : ℚ) ^ 2 * rawEntryRat P z p r (P.b p + k + v))
  have hH : P.H p < p ^ 2 := by
    rw [H_scale P p]
    have := hp.out.pos
    nlinarith
  have hterm (v : ℕ) (hv : v ∈ Finset.range (P.q p + 1)) :
      ((f v).den : ZMod p) ≠ 0 ∧
        R (f v) = R (filterCoeffRat P p v) *
          R ((p : ℚ) ^ 2 * rawEntryRat P z p r (P.b p + k + v)) := by
    have hv' : v ≤ P.q p := by have := Finset.mem_range.mp hv; omega
    have hj : P.b p + k + v < P.H p := by
      have hjL := rawColumn_lt_L hk hv'
      exact lt_of_lt_of_le hjL (by unfold Parameters.H Parameters.C; omega)
    have hraw := (scaledRawEntry_transfer (P := P) (p := p) (N := p) (r := r)
      hp2 hH hj z hzp).1
    exact rational_residue_mul (p := p) (filterCoeff_den P p v) hraw
  have hsum := rational_residue_sum (p := p) (Finset.range (P.q p + 1)) f
    (fun v hv => (hterm v hv).1)
  have hscale : (p : ℚ) ^ 2 * filteredEntryRat P z p r k =
      ∑ v ∈ Finset.range (P.q p + 1), f v := by
    rw [filteredEntryRat, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v hv
    dsimp only [f]
    ring
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact hsum.1
  · change R ((p : ℚ) ^ 2 * filteredEntryRat P z p r k) = _
    rw [hscale]
    calc
      _ = ∑ v ∈ Finset.range (P.q p + 1), R (f v) := hsum.2
      _ = _ := Finset.sum_congr rfl (fun v hv => (hterm v hv).2)

theorem oddPrime_multiple_sum_gather {R : Type*} [Semiring R] {p B : ℕ}
    (hp : 0 < p) (f : ℕ → R) :
    (∑ v ∈ Finset.range (B * p + 1), if v % p = 0 then f v else 0) =
      ∑ u ∈ Finset.range (B + 1), f (u * p) := by
  classical
  refine Finset.sum_bij_ne_zero (fun v _ _ => v / p) ?_ ?_ ?_ ?_
  · intro v hv hfv
    apply Finset.mem_range.mpr
    apply (Nat.div_lt_iff_lt_mul hp).mpr
    have hv' := Finset.mem_range.mp hv
    nlinarith
  · intro v hv hfv w hw hfw hquot
    have hvr : v % p = 0 := by
      by_contra h
      exact hfv (ite_eq_right h)
    have hwr : w % p = 0 := by
      by_contra h
      exact hfw (ite_eq_right h)
    have hdv := Nat.mod_add_div v p
    have hdw := Nat.mod_add_div w p
    rw [hvr, hquot, zero_add] at hdv
    rw [hwr, zero_add] at hdw
    omega
  · intro u hu hfu
    have hu' : u ≤ B := by have := Finset.mem_range.mp hu; omega
    have hbound := Nat.mul_le_mul_right p hu'
    refine ⟨u * p, Finset.mem_range.mpr (by omega), ?_, Nat.mul_div_cancel u hp⟩
    simpa only [Nat.mul_mod_left, ite_eq_left rfl, ite_true] using hfu
  · intro v hv hfv
    have hvr : v % p = 0 := by
      by_contra h
      exact hfv (ite_eq_right h)
    have heq : v / p * p = v := by
      have h := Nat.mod_add_div v p
      rw [hvr, zero_add] at h
      simpa only [Nat.mul_comm] using h
    rw [ite_eq_left hvr, heq]


theorem filtered_block_reduction (P : Parameters) {p : ℕ}
    [hp : Fact p.Prime] (hAdm : Admissible P) (hp2 : p ≠ 2) (hpH : P.H 1 < p) (r0 : Fin P.n0) (i ell : Fin p)
    (k0 : Fin P.n0) (z : ℚ) (hzp : (((p : ℚ) * z).den : ZMod p) ≠ 0) :
    (((p : ℚ) ^ 2 * filteredEntryRat P z p (p * r0.val + i.val)
      (ell.val + p * k0.val)).den : ZMod p) ≠ 0 ∧
      palindromicRatResidue p ((p : ℚ) ^ 2 * filteredEntryRat P z p
        (p * r0.val + i.val) (ell.val + p * k0.val)) =
      extractedFilteredEntry P p r0 i ell k0 := by
  have hcol : ell.val + p * k0.val < P.n p := by
    unfold Parameters.n
    have hb := Nat.mul_le_mul_left p k0.isLt
    have hell := ell.isLt
    nlinarith
  have hs := filteredEntry_scaled_residue_sum P (r := p * r0.val + i.val)
    hp2 hpH hcol z hzp
  refine ⟨hs.1, ?_⟩
  let f : ℕ → ZMod p := fun v =>
    baseFilterWeight P p (v / p) *
      palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat P z p
        (p * r0.val + i.val) (P.b p + (ell.val + p * k0.val) + v))
  have hsum :
      palindromicRatResidue p ((p : ℚ) ^ 2 * filteredEntryRat P z p
        (p * r0.val + i.val) (ell.val + p * k0.val)) =
      ∑ v ∈ Finset.range (P.q0 * p + 1), if v % p = 0 then f v else 0 := by
    calc
      _ = ∑ v ∈ Finset.range (P.q p + 1), palindromicRatResidue p (filterCoeffRat P p v) *
          palindromicRatResidue p ((p : ℚ) ^ 2 * rawEntryRat P z p
            (p * r0.val + i.val) (P.b p + (ell.val + p * k0.val) + v)) := hs.2
      _ = _ := by
        apply Finset.sum_congr rfl
        intro v hv
        have hd := (filterCoeffRat_prime_digit_reduction P (p := p) (v := v)).2
        change palindromicRatResidue p (filterCoeffRat P p v) = _ at hd
        rw [hd]
        split_ifs <;> simp only [f, baseFilterWeight, zero_mul]
  rw [hsum, oddPrime_multiple_sum_gather hp.out.pos]
  unfold extractedFilteredEntry
  apply Finset.sum_congr rfl
  intro u hu
  have hu' : u < P.q0 + 1 := Finset.mem_range.mp hu
  have hk : P.b0 + k0.val + u < P.H 1 := by have := k0.isLt; simp only [Parameters.H, Parameters.C, Parameters.L, Parameters.n, Parameters.b, Parameters.q, Parameters.g, Parameters.h, Nat.mul_one]; omega
  have hindex : P.b p + (ell.val + p * k0.val) + u * p =
      (P.b0 + k0.val + u) * p + ell.val := by unfold Parameters.b; ring
  dsimp only [f]
  rw [Nat.mul_div_cancel u hp.out.pos, hindex,
    (raw_block_reduction P hAdm hp2 hpH r0.isLt i ell hk z hzp).2]

end
end CatalanMeasure.Parametric
