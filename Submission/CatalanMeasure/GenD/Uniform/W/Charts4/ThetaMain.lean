module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.ThetaId
@[expose] public section
set_option Elab.async false

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.Charts3 CatalanMeasure.GenD.Uniform.W.Thin Finset
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

local notation "Fp" => ZMod p

/-- Coefficient polynomials (in `Y`) of the profile coordinates, from the block coefficients. -/
def coefC {b ex : ℕ} (k0 : ℤ) (a : ℕ) (fA fC : ℤ → Fp[X]) (fZ : Fp[X]) : CK b ex → Fp[X]
  | .inl (k, u) =>
    match u.val with
    | 0 => fA (k0 + k) * (X - 1) ^ a
    | 1 => fA (k0 + k) * (X - 1) ^ a * (X - 1)
    | 2 => fC (k0 + k) * (X - 1) ^ a
    | _ => fC (k0 + k) * (X - 1) ^ a * (X - 1)
  | .inr (.inl z) => if z.val = 0 then fZ * (X - 1) ^ a else fZ * (X - 1) ^ a * (X - 1)
  | .inr (.inr _) => 0

theorem cc_A0 {b ex : ℕ} (k0 : ℤ) (a : ℕ) (fA fC : ℤ → Fp[X]) (fZ : Fp[X]) (k : Fin b) :
    coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inl (k, 0)) = fA (k0 + k) * (X - 1) ^ a := rfl
theorem cc_A1 {b ex : ℕ} (k0 : ℤ) (a : ℕ) (fA fC : ℤ → Fp[X]) (fZ : Fp[X]) (k : Fin b) :
    coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inl (k, 1)) = fA (k0 + k) * (X - 1) ^ a * (X - 1) := rfl
theorem cc_C0 {b ex : ℕ} (k0 : ℤ) (a : ℕ) (fA fC : ℤ → Fp[X]) (fZ : Fp[X]) (k : Fin b) :
    coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inl (k, 2)) = fC (k0 + k) * (X - 1) ^ a := rfl
theorem cc_C1 {b ex : ℕ} (k0 : ℤ) (a : ℕ) (fA fC : ℤ → Fp[X]) (fZ : Fp[X]) (k : Fin b) :
    coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inl (k, 3)) = fC (k0 + k) * (X - 1) ^ a * (X - 1) := rfl
theorem cc_Z0 {b ex : ℕ} (k0 : ℤ) (a : ℕ) (fA fC : ℤ → Fp[X]) (fZ : Fp[X]) :
    coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inr (Sum.inl 0)) = fZ * (X - 1) ^ a := rfl
theorem cc_Z1 {b ex : ℕ} (k0 : ℤ) (a : ℕ) (fA fC : ℤ → Fp[X]) (fZ : Fp[X]) :
    coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inr (Sum.inl 1)) = fZ * (X - 1) ^ a * (X - 1) := rfl
theorem cc_X {b ex : ℕ} (k0 : ℤ) (a : ℕ) (fA fC : ℤ → Fp[X]) (fZ : Fp[X]) (j : Fin ex) :
    coefC (b := b) (ex := ex) k0 a fA fC fZ (Sum.inr (Sum.inr j)) = 0 := rfl

section kp
variable (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex : ℕ}

theorem kp_A0 (k : Fin (bN P N p)) (c : Fin (P.n N) → Fp) :
    kindPoly (P := P) (N := N) (ex := ex) hp2 hn (Sum.inl (k, 0)) c =
      fpart p (rem P N p * QA (tL hp2 hn c) k) := by
  simp [kindPoly, lamA, qaL_apply]
theorem kp_A1 (k : Fin (bN P N p)) (c : Fin (P.n N) → Fp) :
    kindPoly (P := P) (N := N) (ex := ex) hp2 hn (Sum.inl (k, 1)) c =
      epart p (rem P N p * QA (tL hp2 hn c) k) := by
  simp [kindPoly, lamA, qaL_apply]
theorem kp_C0 (k : Fin (bN P N p)) (c : Fin (P.n N) → Fp) :
    kindPoly (P := P) (N := N) (ex := ex) hp2 hn (Sum.inl (k, 2)) c =
      fpart p (rem P N p * QC (tL hp2 hn c) k) := by
  simp [kindPoly, lamC, qcL_apply]
theorem kp_C1 (k : Fin (bN P N p)) (c : Fin (P.n N) → Fp) :
    kindPoly (P := P) (N := N) (ex := ex) hp2 hn (Sum.inl (k, 3)) c =
      epart p (rem P N p * QC (tL hp2 hn c) k) := by
  simp [kindPoly, lamC, qcL_apply]
theorem kp_Z0 (c : Fin (P.n N) → Fp) :
    kindPoly (P := P) (N := N) (ex := ex) hp2 hn (Sum.inr (Sum.inl 0)) c =
      fpart p (rem P N p * ((tL hp2 hn c).2 0 • nativeCenter (p := p))) := by
  simp [kindPoly, lamZ, zL_apply]
theorem kp_Z1 (c : Fin (P.n N) → Fp) :
    kindPoly (P := P) (N := N) (ex := ex) hp2 hn (Sum.inr (Sum.inl 1)) c =
      epart p (rem P N p * ((tL hp2 hn c).2 0 • nativeCenter (p := p))) := by
  simp [kindPoly, lamZ, zL_apply]
theorem kp_X (j : Fin ex) (c : Fin (P.n N) → Fp) :
    kindPoly (P := P) (N := N) hp2 hn (Sum.inr (Sum.inr j)) c = 0 := by
  simp [kindPoly]
end kp

theorem collapse (hp2 : p ≠ 2) (hn : 1 ≤ P.n N) {ex K : ℕ} (hK : K = bN P N p * 4 + 2 + ex)
    (fA fC : ℤ → Fp[X]) (fZ : Fp[X]) (c : Fin (P.n N) → Fp) :
    ∑ e : Fin p, X ^ (e : ℕ) * (sumProf hK (coefC (k0N P N p) (P.h N / p) fA fC fZ)
        (Theta hp2 hn hK c e)).comp (X ^ p) =
      (X ^ p - 1) ^ (P.h N / p) * rem P N p *
        (∑ k : Fin (bN P N p), ((fA (k0N P N p + k)).comp (X ^ p) * QA (tL hp2 hn c) k +
            (fC (k0N P N p + k)).comp (X ^ p) * QC (tL hp2 hn c) k) +
          fZ.comp (X ^ p) * ((tL hp2 hn c).2 0 • nativeCenter (p := p))) := by
  rw [Theta_sum]
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [Fin.sum_univ_four, Fin.sum_univ_two]
  have hk : ∀ k : Fin (bN P N p),
      (kindPoly (ex := ex) hp2 hn (Sum.inl (k, (0 : Fin 4))) c *
          (coefC (k0N P N p) (P.h N / p) fA fC fZ (Sum.inl (k, (0 : Fin 4)) : CK (bN P N p) ex)).comp (X ^ p) +
        kindPoly (ex := ex) hp2 hn (Sum.inl (k, (1 : Fin 4))) c *
          (coefC (k0N P N p) (P.h N / p) fA fC fZ (Sum.inl (k, (1 : Fin 4)) : CK (bN P N p) ex)).comp (X ^ p) +
        kindPoly (ex := ex) hp2 hn (Sum.inl (k, (2 : Fin 4))) c *
          (coefC (k0N P N p) (P.h N / p) fA fC fZ (Sum.inl (k, (2 : Fin 4)) : CK (bN P N p) ex)).comp (X ^ p) +
        kindPoly (ex := ex) hp2 hn (Sum.inl (k, (3 : Fin 4))) c *
          (coefC (k0N P N p) (P.h N / p) fA fC fZ (Sum.inl (k, (3 : Fin 4)) : CK (bN P N p) ex)).comp (X ^ p)) =
      (X ^ p - 1) ^ (P.h N / p) * rem P N p *
        ((fA (k0N P N p + k)).comp (X ^ p) * QA (tL hp2 hn c) k +
          (fC (k0N P N p + k)).comp (X ^ p) * QC (tL hp2 hn c) k) := by
    intro k
    rw [kp_A0 hp2 hn, kp_A1 hp2 hn, kp_C0 hp2 hn, kp_C1 hp2 hn]
    have s1 := slot_comb (rem P N p * QA (tL hp2 hn c) k)
      ((fA (k0N P N p + k)).comp (X ^ p) * (X ^ p - 1) ^ (P.h N / p))
    have s2 := slot_comb (rem P N p * QC (tL hp2 hn c) k)
      ((fC (k0N P N p + k)).comp (X ^ p) * (X ^ p - 1) ^ (P.h N / p))
    rw [cc_A0, cc_A1, cc_C0, cc_C1]
    simp only [mul_comp, pow_comp, sub_comp, X_comp, one_comp]
    linear_combination s1 + s2
  have hz : (kindPoly (ex := ex) hp2 hn (Sum.inr (Sum.inl (0 : Fin 2))) c *
          (coefC (k0N P N p) (P.h N / p) fA fC fZ (Sum.inr (Sum.inl (0 : Fin 2)) : CK (bN P N p) ex)).comp (X ^ p) +
        kindPoly (ex := ex) hp2 hn (Sum.inr (Sum.inl (1 : Fin 2))) c *
          (coefC (k0N P N p) (P.h N / p) fA fC fZ (Sum.inr (Sum.inl (1 : Fin 2)) : CK (bN P N p) ex)).comp (X ^ p)) =
      (X ^ p - 1) ^ (P.h N / p) * rem P N p * (fZ.comp (X ^ p) * ((tL hp2 hn c).2 0 • nativeCenter (p := p))) := by
    rw [kp_Z0 hp2 hn, kp_Z1 hp2 hn]
    have s := slot_comb (rem P N p * ((tL hp2 hn c).2 0 • nativeCenter (p := p)))
      (fZ.comp (X ^ p) * (X ^ p - 1) ^ (P.h N / p))
    rw [cc_Z0, cc_Z1]
    simp only [mul_comp, pow_comp, sub_comp, X_comp, one_comp]
    linear_combination s
  have hx : ∑ j : Fin ex, kindPoly (P := P) (N := N) hp2 hn (Sum.inr (Sum.inr j)) c *
      (coefC (k0N P N p) (P.h N / p) fA fC fZ (Sum.inr (Sum.inr j) : CK (bN P N p) ex)).comp (X ^ p) = 0 := by
    simp [kp_X, cc_X]
  rw [hx, add_zero, hz, Finset.sum_congr rfl (fun k _ => hk k), ← Finset.mul_sum]
  ring

end
end CatalanMeasure.GenD.Uniform.W.Charts4
