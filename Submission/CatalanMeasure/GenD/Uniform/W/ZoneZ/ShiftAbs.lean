module
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.RawResponseDigit
@[expose] public section
set_option Elab.async false

/-!
# Shift Lemma, abstract form

`Φ(J+1,S+1) = Φ(J,S) + ψ_S/(J+1) + boundary` for the finite source covector `digitPhi`
(zone2 sec. 4: every Lemma-S pattern `1/(J+1)`, `1/J` comes from this).

The moment sequences enter only through the one-step relations
`M(J+1)(i+2) = M(J)(i+1) - μ_i r`, `M(J+1) 1 = M(J) 0`, `Z(J+1)(w+1) = Z(J) w - ν_w r`
(`r = 1/(J+1)`), which hold for the actual moments (`ShiftMoments`).
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial Finset CatalanMeasure.GenD.Uniform.Prefix
noncomputable section
variable {R : Type*} [CommRing R]

/-- The `J`-independent part `ψ_S` of the shift. -/
def shiftPsi (S : ℕ) (a b : R[X]) (c : R) (μ ν : ℕ → R) : R :=
  -(∑ i ∈ range (S + 2), intrinsicCoeff a ((S : ℤ) - i) * μ i) +
    c * ∑ w ∈ range (S + 2), intrinsicCoeff b ((S : ℤ) - w) * ν w

/-- The two boundary terms, which vanish for `deg a ≤ S+1`, `deg b ≤ S`. -/
def shiftBdry (S : ℕ) (a b : R[X]) (c : R) (M1 Z1 : ℕ → R) : R :=
  intrinsicCoeff a ((S : ℤ) + 2) * M1 0 - c * intrinsicCoeff b ((S : ℤ) + 1) * Z1 0

theorem digitPhi_shift (S : ℕ) (a b : R[X]) (c r : R) (M0 M1 Z0 Z1 μ ν : ℕ → R)
    (hM0 : M1 1 = M0 0) (hMs : ∀ i, i < S + 2 → M1 (i + 2) = M0 (i + 1) - μ i * r)
    (hZs : ∀ w, w < S + 2 → Z1 (w + 1) = Z0 w - ν w * r) :
    digitPhi (S + 3) ((S : ℤ) + 1) M1 Z1 a b c =
      digitPhi (S + 3) (S : ℤ) M0 Z0 a b c + r * shiftPsi S a b c μ ν +
        shiftBdry S a b c M1 Z1 := by
  unfold digitPhi shiftPsi shiftBdry
  -- M part
  have hMa : ∑ v ∈ range (S + 3 + 1), intrinsicCoeff a ((S : ℤ) + 1 + 1 - v) * M1 v =
      intrinsicCoeff a ((S : ℤ) + 2) * M1 0 + intrinsicCoeff a ((S : ℤ) + 1) * M0 0 +
        (∑ i ∈ range (S + 2), intrinsicCoeff a ((S : ℤ) - i) * M0 (i + 1)) -
        r * ∑ i ∈ range (S + 2), intrinsicCoeff a ((S : ℤ) - i) * μ i := by
    rw [Finset.sum_range_succ' _ (S + 3), Finset.sum_range_succ' _ (S + 2)]
    have e1 : ∀ i ∈ range (S + 2), intrinsicCoeff a ((S : ℤ) + 1 + 1 - ((i + 1 + 1 : ℕ) : ℤ)) *
        M1 (i + 1 + 1) = intrinsicCoeff a ((S : ℤ) - i) * M0 (i + 1) -
          r * (intrinsicCoeff a ((S : ℤ) - i) * μ i) := by
      intro i hi
      rw [hMs i (Finset.mem_range.mp hi)]
      have : (S : ℤ) + 1 + 1 - ((i + 1 + 1 : ℕ) : ℤ) = (S : ℤ) - i := by push_cast; ring
      rw [this]; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e2 : (S : ℤ) + 1 + 1 - ((0 + 1 : ℕ) : ℤ) = (S : ℤ) + 1 := by push_cast; ring
    have e3 : (S : ℤ) + 1 + 1 - ((0 : ℕ) : ℤ) = (S : ℤ) + 2 := by push_cast; ring
    simp only [e2, e3, zero_add, hM0]
    ring
  have hMb : ∑ v ∈ range (S + 3 + 1), intrinsicCoeff a ((S : ℤ) + 1 - v) * M0 v =
      intrinsicCoeff a ((S : ℤ) + 1) * M0 0 +
        ∑ i ∈ range (S + 2), intrinsicCoeff a ((S : ℤ) - i) * M0 (i + 1) := by
    rw [Finset.sum_range_succ' _ (S + 3), Finset.sum_range_succ _ (S + 2)]
    have e4 : intrinsicCoeff a ((S : ℤ) + 1 - ((S + 2 + 1 : ℕ) : ℤ)) = 0 := by
      unfold intrinsicCoeff; rw [if_neg]; push_cast; omega
    have e5 : ∀ i : ℕ, (S : ℤ) + 1 - ((i + 1 : ℕ) : ℤ) = (S : ℤ) - i := by
      intro i; push_cast; ring
    have e7 : intrinsicCoeff a ((S : ℤ) - ((S + 2 : ℕ) : ℤ)) = 0 := by
      unfold intrinsicCoeff; rw [if_neg]; push_cast; omega
    simp only [e5, e4, e7, zero_mul, add_zero]
    have e6 : (S : ℤ) + 1 - ((0 : ℕ) : ℤ) = (S : ℤ) + 1 := by push_cast; ring
    rw [e6]; ring
  -- Z part
  have hZa : ∑ v ∈ range (S + 3), intrinsicCoeff b ((S : ℤ) + 1 - v) * Z1 v =
      intrinsicCoeff b ((S : ℤ) + 1) * Z1 0 +
        (∑ w ∈ range (S + 2), intrinsicCoeff b ((S : ℤ) - w) * Z0 w) -
        r * ∑ w ∈ range (S + 2), intrinsicCoeff b ((S : ℤ) - w) * ν w := by
    rw [Finset.sum_range_succ' _ (S + 2)]
    have e1 : ∀ w ∈ range (S + 2), intrinsicCoeff b ((S : ℤ) + 1 - ((w + 1 : ℕ) : ℤ)) *
        Z1 (w + 1) = intrinsicCoeff b ((S : ℤ) - w) * Z0 w -
          r * (intrinsicCoeff b ((S : ℤ) - w) * ν w) := by
      intro w hw
      rw [hZs w (Finset.mem_range.mp hw)]
      have : (S : ℤ) + 1 - ((w + 1 : ℕ) : ℤ) = (S : ℤ) - w := by push_cast; ring
      rw [this]; ring
    rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have e3 : (S : ℤ) + 1 - ((0 : ℕ) : ℤ) = (S : ℤ) + 1 := by push_cast; ring
    rw [e3]; ring
  have hZb : ∑ v ∈ range (S + 3), intrinsicCoeff b ((S : ℤ) - v) * Z0 v =
      ∑ w ∈ range (S + 2), intrinsicCoeff b ((S : ℤ) - w) * Z0 w := by
    rw [Finset.sum_range_succ _ (S + 2)]
    have e4 : intrinsicCoeff b ((S : ℤ) - ((S + 2 : ℕ) : ℤ)) = 0 := by
      unfold intrinsicCoeff; rw [if_neg]; push_cast; omega
    rw [e4, zero_mul, add_zero]
  rw [hMa, hMb, hZa, hZb]
  ring

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
