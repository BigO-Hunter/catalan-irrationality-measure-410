module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ChebCoeff
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.TpSystem
@[expose] public section
set_option Elab.async false

/-!
# Integer-index Chebyshev coefficients and profile combinations (MT (b) glue cells)

`tI κ`, `uI κ` are the integer coefficient functions of `T_κ`, `U_κ` for **integer** `κ` (the block
offset `k0` of the glue cells is `-1`); `y2uI`, `xuI`, `xtI` are those of `(X²-1) U_{κ-1}`,
`(X-1) U_{κ-1}`, `(X-1) T_κ`.  `cmb z k0 K g` is the coefficient function of the profile combination
`Σ_{k<K} z_k g(k0+k)`.  `coeff_*` identify the coefficients of the polynomials `tyMap`, `gyMap`,
`tpTy`, `tpGy` of an integer profile `k ↦ z_k` over `ZMod p`.
-/

namespace CatalanMeasure.GenD.Uniform.W.MTGlue
open Polynomial OAI.InternalCatalan CatalanMeasure.GenD.Uniform.W.ZoneZ
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.SlotsT

/-- Coefficient of `x^i` in `T_κ`, `κ ∈ ℤ`. -/
def tI (κ : ℤ) (i : ℕ) : ℤ := Q.tc κ.natAbs i

/-- Coefficient of `x^i` in `U_κ`, `κ ∈ ℤ` (`U_{-1} = 0`, `U_{-κ-2} = -U_κ`). -/
def uI (κ : ℤ) (i : ℕ) : ℤ :=
  if 0 ≤ κ then Q.uc κ.toNat i else if κ = -1 then 0 else - Q.uc (-κ - 2).toNat i

/-- Coefficient of `x^n` in `(X²-1) U_{κ-1}`. -/
def y2uI (κ : ℤ) (n : ℕ) : ℤ := (if n < 2 then 0 else uI (κ - 1) (n - 2)) - uI (κ - 1) n

/-- Coefficient of `x^n` in `(X-1) U_{κ-1}`. -/
def xuI (κ : ℤ) (n : ℕ) : ℤ := (if n = 0 then 0 else uI (κ - 1) (n - 1)) - uI (κ - 1) n

/-- Coefficient of `x^n` in `(X-1) T_κ`. -/
def xtI (κ : ℤ) (n : ℕ) : ℤ := (if n = 0 then 0 else tI κ (n - 1)) - tI κ n

/-- Coefficient function of `Σ_{k<K} z_k g(k0+k)`. -/
def cmb (z : ℕ → ℤ) (k0 : ℤ) (K : ℕ) (g : ℤ → ℕ → ℤ) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range K, z k * g (k0 + (k : ℤ)) n

section Cheb
variable (R : Type*) [CommRing R]

theorem T_coeffI (κ : ℤ) (i : ℕ) : (Chebyshev.T R κ).coeff i = (tI κ i : R) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg κ
  · rw [T_coeff]; simp [tI]
  · rw [Chebyshev.T_neg, T_coeff]; simp [tI]

theorem U_coeffI (κ : ℤ) (i : ℕ) : (Chebyshev.U R κ).coeff i = (uI κ i : R) := by
  by_cases h0 : 0 ≤ κ
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [U_coeff]; simp [uI]
  · by_cases h1 : κ = -1
    · subst h1; simp [uI, Chebyshev.U_neg_one]
    · have h2 : ∃ n : ℕ, κ = -(n : ℤ) - 2 := ⟨(-κ - 2).toNat, by omega⟩
      obtain ⟨n, rfl⟩ := h2
      rw [Chebyshev.U_neg_sub_two, coeff_neg, U_coeff]
      have hn : (-(-(n : ℤ) - 2) - 2).toNat = n := by omega
      have e1 : ¬ (0 ≤ -(n : ℤ) - 2) := by omega
      have e2 : ¬ (-(n : ℤ) - 2 = -1) := by omega
      simp [uI, e1, e2, hn]

theorem y2u_coeff (κ : ℤ) (n : ℕ) :
    ((X ^ 2 - 1 : R[X]) * Chebyshev.U R (κ - 1)).coeff n = (y2uI κ n : R) := by
  rw [sub_mul, coeff_sub, one_mul, coeff_X_pow_mul']
  simp only [U_coeffI]
  by_cases h : 2 ≤ n
  · rw [if_pos h]; simp [y2uI, show ¬ n < 2 from by omega]
  · rw [if_neg h]; simp [y2uI, show n < 2 from by omega]

theorem xm1_coeff (Q : R[X]) (n : ℕ) :
    ((X - 1 : R[X]) * Q).coeff n = (if n = 0 then 0 else Q.coeff (n - 1)) - Q.coeff n := by
  rw [sub_mul, coeff_sub, one_mul]
  rcases n with _ | n
  · simp
  · rw [coeff_X_mul]; simp

theorem xu_coeff (κ : ℤ) (n : ℕ) :
    ((X - 1 : R[X]) * Chebyshev.U R (κ - 1)).coeff n = (xuI κ n : R) := by
  rw [xm1_coeff]
  simp only [U_coeffI, xuI]
  split_ifs <;> simp

theorem xt_coeff (κ : ℤ) (n : ℕ) :
    ((X - 1 : R[X]) * Chebyshev.T R κ).coeff n = (xtI κ n : R) := by
  rw [xm1_coeff]
  simp only [T_coeffI, xtI]
  split_ifs <;> simp

end Cheb

variable {p : ℕ} [Fact p.Prime]

/-- The integer profile `k ↦ z_k` over `ZMod p`. -/
def zprof (p : ℕ) (K : ℕ) (z : ℕ → ℤ) : Fin K → ZMod p := fun k => ((z k : ℤ) : ZMod p)

theorem coeff_combo (K : ℕ) (z : ℕ → ℤ) (Qf : ℕ → (ZMod p)[X]) (gf : ℕ → ℕ → ℤ)
    (h : ∀ k n, (Qf k).coeff n = (gf k n : ZMod p)) (n : ℕ) :
    (∑ k : Fin K, C ((zprof p K z) k) * Qf k).coeff n =
      ((∑ k ∈ Finset.range K, z k * gf k n : ℤ) : ZMod p) := by
  rw [finsetSum_coeff]
  simp only [coeff_C_mul, h, zprof]
  rw [Fin.sum_univ_eq_sum_range (fun k => ((z k : ℤ) : ZMod p) * ((gf k n : ℤ) : ZMod p)) K]
  push_cast; rfl

theorem tyMap_coeff (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) (n : ℕ) :
    (tyMap p K k0 (zprof p K z)).coeff n = (cmb z k0 K tI n : ZMod p) := by
  rw [tyMap_apply]
  exact coeff_combo K z (fun k => Chebyshev.T (ZMod p) (k0 + (k : ℤ))) (fun k n => tI (k0 + k) n)
    (fun k n => T_coeffI _ _ _) n

theorem gyMap_coeff (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) (n : ℕ) :
    (gyMap p K k0 (zprof p K z)).coeff n = (cmb z k0 K y2uI n : ZMod p) := by
  rw [gyMap_apply, uyMap_apply, Finset.mul_sum]
  have : ∀ k : Fin K, (X ^ 2 - 1 : (ZMod p)[X]) * (C ((zprof p K z) k) *
      Chebyshev.U (ZMod p) (k0 + ((k : ℕ) : ℤ) - 1)) =
      C ((zprof p K z) k) * ((X ^ 2 - 1) * Chebyshev.U (ZMod p) ((k0 + ((k : ℕ) : ℤ)) - 1)) :=
    fun k => by ring
  simp only [this]
  exact coeff_combo K z (fun k => (X ^ 2 - 1) * Chebyshev.U (ZMod p) ((k0 + (k : ℤ)) - 1))
    (fun k n => y2uI (k0 + k) n) (fun k n => y2u_coeff _ _ _) n

theorem tpTy_coeff (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) (n : ℕ) :
    (tpTy p K k0 (zprof p K z)).coeff n = (cmb z k0 K xuI n : ZMod p) := by
  rw [tpTy_apply, Finset.mul_sum]
  have : ∀ k : Fin K, (X - 1 : (ZMod p)[X]) * (C ((zprof p K z) k) *
      Chebyshev.U (ZMod p) (k0 + ((k : ℕ) : ℤ) - 1)) =
      C ((zprof p K z) k) * ((X - 1) * Chebyshev.U (ZMod p) ((k0 + ((k : ℕ) : ℤ)) - 1)) :=
    fun k => by ring
  simp only [this]
  exact coeff_combo K z (fun k => (X - 1) * Chebyshev.U (ZMod p) ((k0 + (k : ℤ)) - 1))
    (fun k n => xuI (k0 + k) n) (fun k n => xu_coeff _ _ _) n

theorem tpGy_coeff (K : ℕ) (k0 : ℤ) (z : ℕ → ℤ) (n : ℕ) :
    (tpGy p K k0 (zprof p K z)).coeff n = (cmb z k0 K xtI n : ZMod p) := by
  rw [tpGy_apply, Finset.mul_sum]
  have : ∀ k : Fin K, (X - 1 : (ZMod p)[X]) * (C ((zprof p K z) k) *
      Chebyshev.T (ZMod p) (k0 + ((k : ℕ) : ℤ))) =
      C ((zprof p K z) k) * ((X - 1) * Chebyshev.T (ZMod p) (k0 + ((k : ℕ) : ℤ))) :=
    fun k => by ring
  simp only [this]
  exact coeff_combo K z (fun k => (X - 1) * Chebyshev.T (ZMod p) (k0 + (k : ℤ)))
    (fun k n => xtI (k0 + k) n) (fun k n => xt_coeff _ _ _) n

end CatalanMeasure.GenD.Uniform.W.MTGlue
end
