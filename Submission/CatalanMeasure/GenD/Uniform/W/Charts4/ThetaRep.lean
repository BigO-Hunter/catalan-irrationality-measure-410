module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.ThetaMain
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.OfForward
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.W.Thin Finset
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

/-- Coefficients of `Ty` (the `U`-side pair coefficients `b_τ`). -/
def uCoefs {b ex : ℕ} (k0 : ℤ) (a : ℕ) : CK b ex → Fp[X] :=
  coefC k0 a (fun κ => U Fp κ + U Fp (κ - 1)) (fun κ => U Fp κ - U Fp (κ - 1)) (U Fp (k0 - 1))

/-- Coefficients of `Gy` (the `T`-side pair coefficients `a_τ`). -/
def tCoefs {b ex : ℕ} (k0 : ℤ) (a : ℕ) : CK b ex → Fp[X] :=
  coefC k0 a (fun κ => (1 + X) * (U Fp κ - U Fp (κ - 1))) (fun κ => (X - 1) * (U Fp κ + U Fp (κ - 1)))
    (T Fp k0)

/-- The profile maps of the four-point frame. -/
def monoProfile (P : Parameters) (N p : ℕ) [Fact p.Prime] {ex K : ℕ}
    (hK : K = bN P N p * 4 + 2 + ex) : Prof p K where
  Ty := sumProf hK (uCoefs (k0N P N p) (P.h N / p))
  Gy := sumProf hK (tCoefs (k0N P N p) (P.h N / p))

theorem intrinsicU_eq (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (c : Fin (P.n N) → Fp) :
    intrinsicU P N p c = ∑ i : Fin (bN P N p * p + 1), C (rowsExt (P.n N) (P.g N) p
        (Fact.out : p.Prime).pos hn c i) * U Fp (k0N P N p * p + ((i : ℕ) : ℤ) - 1) := by
  have hp := (Fact.out : p.Prime).pos
  simp_rw [← smul_eq_C_mul]
  rw [rowsExt_sum (P.n N) (P.g N) p (R := Fp[X]) hp hn c (fun i => U Fp (k0N P N p * p + (i : ℤ) - 1))]
  unfold intrinsicU
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_eq_C_mul]
  congr 2
  have := (gja_spec (g := P.g N) hp).1
  push_cast
  show _ = _
  simp only [k0N]
  linarith

theorem intrinsicT_eq (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) (c : Fin (P.n N) → Fp) :
    nativeCenter (p := p) * intrinsicT P N p c =
      ∑ i : Fin (bN P N p * p + 1), C (rowsExt (P.n N) (P.g N) p
        (Fact.out : p.Prime).pos hn c i) * (nativeCenter (p := p) * T Fp (k0N P N p * p + ((i : ℕ) : ℤ))) := by
  have hp := (Fact.out : p.Prime).pos
  simp_rw [← smul_eq_C_mul]
  rw [rowsExt_sum (P.n N) (P.g N) p (R := Fp[X]) hp hn c
    (fun i => nativeCenter (p := p) * T Fp (k0N P N p * p + (i : ℤ)))]
  unfold intrinsicT
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_eq_C_mul]
  have := (gja_spec (g := P.g N) hp).1
  have e : k0N P N p * p + ((gja (P.g N) p + (r : ℕ) : ℕ) : ℤ) = (r : ℤ) - P.g N := by
    push_cast
    simp only [k0N]
    linarith
  rw [e]
  ring

theorem Theta_repU (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex K : ℕ} (hK : K = bN P N p * 4 + 2 + ex)
    (c : Fin (P.n N) → Fp) :
    (X - 1) ^ P.h N * intrinsicU P N p c =
      ∑ e : Fin p, X ^ (e : ℕ) * ((monoProfile P N p hK).Ty (Theta hp2 hn hK c e)).comp (X ^ p) := by
  show _ = ∑ e : Fin p, X ^ (e : ℕ) * (sumProf hK (uCoefs (k0N P N p) (P.h N / p))
      (Theta hp2 hn hK c e)).comp (X ^ p)
  rw [uCoefs, collapse hp2 hn hK, intrinsicU_eq hp2 hn c]
  have hfrob : (X - 1 : Fp[X]) ^ P.h N = (X ^ p - 1) ^ (P.h N / p) * rem P N p :=
    omega_frobenius (R := Fp) (P.h N)
  have ht := tiling_U hp2 (bN P N p) (k0N P N p) (tL hp2 hn c)
  have hsym : physicalTilingEquiv (bN P N p) ((p - 1) / 2) p (native_half_identity hp2)
      (native_two_ne_zero hp2) (tL hp2 hn c) = rowsExt (P.n N) (P.g N) p (Fact.out : p.Prime).pos hn c := by
    simp [tL]
  rw [hsym] at ht
  rw [hfrob, ht]
  simp only [blkP, blkM]

theorem Theta_repT (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex K : ℕ} (hK : K = bN P N p * 4 + 2 + ex)
    (c : Fin (P.n N) → Fp) :
    (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * intrinsicT P N p c =
      ∑ e : Fin p, X ^ (e : ℕ) * ((monoProfile P N p hK).Gy (Theta hp2 hn hK c e)).comp (X ^ p) := by
  show _ = ∑ e : Fin p, X ^ (e : ℕ) * (sumProf hK (tCoefs (k0N P N p) (P.h N / p))
      (Theta hp2 hn hK c e)).comp (X ^ p)
  rw [tCoefs, collapse hp2 hn hK]
  have hfrob : (X - 1 : Fp[X]) ^ P.h N = (X ^ p - 1) ^ (P.h N / p) * rem P N p :=
    omega_frobenius (R := Fp) (P.h N)
  have ht := tiling_T hp2 (bN P N p) (k0N P N p) (tL hp2 hn c)
  have hsym : physicalTilingEquiv (bN P N p) ((p - 1) / 2) p (native_half_identity hp2)
      (native_two_ne_zero hp2) (tL hp2 hn c) = rowsExt (P.n N) (P.g N) p (Fact.out : p.Prime).pos hn c := by
    simp [tL]
  rw [hsym, ← intrinsicT_eq hp2 hn c] at ht
  have hw : (X ^ 2 - 1 : Fp[X]) ^ ((p - 1) / 2) = nativeCenter (p := p) := rfl
  rw [hw, hfrob]
  have := congrArg (fun q => (X ^ p - 1) ^ (P.h N / p) * rem P N p * q) ht
  simp only [blkGA, blkGC, blkM, blkP, mul_comp, add_comp, sub_comp, one_comp, X_comp] at this ⊢
  linear_combination this

end
end CatalanMeasure.GenD.Uniform.W.Charts4
