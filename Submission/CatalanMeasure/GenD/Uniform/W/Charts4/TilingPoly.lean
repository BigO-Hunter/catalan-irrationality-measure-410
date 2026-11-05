module
public import Submission.CatalanMeasure.GenD.Uniform.W.Charts4.TilingSum
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.NativeSpans
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.NativeSlots
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.PhysicalPairs
@[expose] public section
set_option Elab.async false

/-!
# The tiling in the native slot basis (U and T sides)

For tiling coordinates `t` over `F_p` (`p = 2h+1`, `b` blocks) let

* `QA t k = u_{k+1} w + Σ_j sym_{kj} nativePlus (j+1)`  (the H+ slot polynomial of block `k`),
* `QC t k = Σ_j asym_{kj} nativeMinus (j+1)`            (the H- slot polynomial),
* `u_0 w`                                               (the outer centre slot),

with `w = nativeCenter = (X^2-1)^h = U_{p-1}`.  Then, over the ENLARGED rows (no virtual-row
restriction),

    Σ_i rows_i U_{k0 p + i - 1}       = Σ_k ( P_κ(Y) QA_k + M_κ(Y) QC_k ) + U_{k0-1}(Y) u_0 w
    w · Σ_i rows_i T_{k0 p + i}        = Σ_k ( GA_κ(Y) QA_k + GC_κ(Y) QC_k ) + T_{k0}(Y) u_0 w

with `κ = k0 + k`, `Y = X^p`, `P_κ = U_κ + U_{κ-1}`, `M_κ = U_κ - U_{κ-1}`, `GA_κ = (1+Y) M_κ`,
`GC_κ = (Y-1) P_κ` (the `b_τ, a_τ` pair coefficients of the paper, section 4).
-/

namespace CatalanMeasure.GenD.Uniform.W.Charts4
open CatalanMeasure.GenD.Uniform.Prefix Polynomial Polynomial.Chebyshev Finset
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- `P_κ(Y) = (U_κ + U_{κ-1})(X^p)`. -/
def blkP (p : ℕ) [Fact p.Prime] (κ : ℤ) : (ZMod p)[X] :=
  (U (ZMod p) κ + U (ZMod p) (κ - 1)).comp (X ^ p)

/-- `M_κ(Y) = (U_κ - U_{κ-1})(X^p)`. -/
def blkM (p : ℕ) [Fact p.Prime] (κ : ℤ) : (ZMod p)[X] :=
  (U (ZMod p) κ - U (ZMod p) (κ - 1)).comp (X ^ p)

/-- `GA_κ = (1+Y) M_κ(Y)`. -/
def blkGA (p : ℕ) [Fact p.Prime] (κ : ℤ) : (ZMod p)[X] := (1 + X ^ p) * blkM p κ

/-- `GC_κ = (Y-1) P_κ(Y)`. -/
def blkGC (p : ℕ) [Fact p.Prime] (κ : ℤ) : (ZMod p)[X] := (X ^ p - 1) * blkP p κ

/-- The H+ slot polynomial of block `k`. -/
def QA {b : ℕ} (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2)) (k : Fin b) : (ZMod p)[X] :=
  t.2 k.succ • nativeCenter (p := p) +
    ∑ j : Fin ((p - 1) / 2), t.1.1 (finProdFinEquiv (k, j)) • nativePlus (p := p) ((j : ℤ) + 1)

/-- The H- slot polynomial of block `k`. -/
def QC {b : ℕ} (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2)) (k : Fin b) : (ZMod p)[X] :=
  ∑ j : Fin ((p - 1) / 2), t.1.2 (finProdFinEquiv (k, j)) • nativeMinus (p := p) ((j : ℤ) + 1)

theorem pairU_plus (hp2 : p ≠ 2) (κ j : ℤ) :
    U (ZMod p) (κ * p + j - 1) + U (ZMod p) ((κ + 1) * p - j - 1) =
      blkP p κ * nativePlus (p := p) j := by
  have h1 := physical_pair_U_plus (ZMod p) κ p j
  rw [CatalanMeasure.Parametric.chebyshev_T_prime hp2,
    CatalanMeasure.Parametric.chebyshev_U_prime hp2] at h1
  rw [h1, nativePlus_formula hp2 j]
  simp only [blkP, add_comp, nativeCenter]

theorem pairU_minus (hp2 : p ≠ 2) (κ j : ℤ) :
    U (ZMod p) (κ * p + j - 1) - U (ZMod p) ((κ + 1) * p - j - 1) =
      blkM p κ * nativeMinus (p := p) j := by
  have h1 := physical_pair_U_minus (ZMod p) κ p j
  rw [CatalanMeasure.Parametric.chebyshev_T_prime hp2,
    CatalanMeasure.Parametric.chebyshev_U_prime hp2] at h1
  rw [h1, nativeMinus_formula hp2 j]
  simp only [blkM, sub_comp, nativeCenter]

theorem pairT_plus (hp2 : p ≠ 2) (κ j : ℤ) :
    nativeCenter (p := p) * (T (ZMod p) (κ * p + j) + T (ZMod p) ((κ + 1) * p - j)) =
      blkGA p κ * nativePlus (p := p) j := by
  have h1 := physical_pair_T_plus (ZMod p) κ p j
  rw [CatalanMeasure.Parametric.chebyshev_T_prime hp2,
    CatalanMeasure.Parametric.chebyshev_U_prime hp2] at h1
  rw [nativePlus_formula hp2 j]
  have : nativeCenter (p := p) = (X ^ 2 - 1) ^ ((p - 1) / 2) := rfl
  rw [this, h1]
  simp only [blkGA, blkM, sub_comp]

theorem pairT_minus (hp2 : p ≠ 2) (κ j : ℤ) :
    nativeCenter (p := p) * (T (ZMod p) (κ * p + j) - T (ZMod p) ((κ + 1) * p - j)) =
      blkGC p κ * nativeMinus (p := p) j := by
  have h1 := physical_pair_T_minus (ZMod p) κ p j
  rw [CatalanMeasure.Parametric.chebyshev_T_prime hp2,
    CatalanMeasure.Parametric.chebyshev_U_prime hp2] at h1
  rw [nativeMinus_formula hp2 j]
  have : nativeCenter (p := p) = (X ^ 2 - 1) ^ ((p - 1) / 2) := rfl
  rw [this, h1]
  simp only [blkGC, blkP, add_comp]

/-- The generic assembly: pair relations for `F` give the slot-basis expansion. -/
theorem tiling_poly (hp2 : p ≠ 2) (b : ℕ) (t : TilingCoordinates (K := ZMod p) b ((p - 1) / 2))
    (F : ℕ → (ZMod p)[X]) (P Mm : Fin b → (ZMod p)[X]) (c0 : (ZMod p)[X])
    (hP : ∀ (k : Fin b) (j : Fin ((p - 1) / 2)),
      F (k * p + (j + 1)) + F (k * p + (p - (j + 1))) = P k * nativePlus (p := p) ((j : ℤ) + 1))
    (hM : ∀ (k : Fin b) (j : Fin ((p - 1) / 2)),
      F (k * p + (j + 1)) - F (k * p + (p - (j + 1))) = Mm k * nativeMinus (p := p) ((j : ℤ) + 1))
    (hE : ∀ k : Fin b, F (k * p) + F ((k + 1) * p) = P k * nativeCenter (p := p))
    (h0 : F 0 = c0 * nativeCenter (p := p)) :
    ∑ i : Fin (b * p + 1), C (physicalTilingEquiv b ((p - 1) / 2) p (native_half_identity hp2)
        (native_two_ne_zero hp2) t i) * F i =
      ∑ k : Fin b, (P k * QA t k + Mm k * QC t k) + c0 * (t.2 0 • nativeCenter (p := p)) := by
  have hs := tiling_sum (K := ZMod p) (M := (ZMod p)[X]) b ((p - 1) / 2) p
    (native_half_identity hp2) (native_two_ne_zero hp2) t F
  have hC : ∀ i : Fin (b * p + 1), C (physicalTilingEquiv b ((p - 1) / 2) p
      (native_half_identity hp2) (native_two_ne_zero hp2) t i) * F i =
      (physicalTilingEquiv b ((p - 1) / 2) p (native_half_identity hp2)
        (native_two_ne_zero hp2) t i) • F i := fun i => (smul_eq_C_mul _).symm
  simp_rw [hC]
  rw [hs]
  simp only [hP, hM, hE, h0]
  have e : ∀ k : Fin b, (∑ j : Fin ((p - 1) / 2),
      (t.1.1 (finProdFinEquiv (k, j)) • (P k * nativePlus (p := p) ((j : ℤ) + 1)) +
       t.1.2 (finProdFinEquiv (k, j)) • (Mm k * nativeMinus (p := p) ((j : ℤ) + 1)))) +
      t.2 k.succ • (P k * nativeCenter (p := p)) = P k * QA t k + Mm k * QC t k := by
    intro k
    simp only [QA, QC, mul_add, Finset.mul_sum, mul_smul_comm, Finset.sum_add_distrib]
    abel
  have hsum : (∑ k : Fin b, ∑ j : Fin ((p - 1) / 2),
      (t.1.1 (finProdFinEquiv (k, j)) • (P k * nativePlus (p := p) ((j : ℤ) + 1)) +
       t.1.2 (finProdFinEquiv (k, j)) • (Mm k * nativeMinus (p := p) ((j : ℤ) + 1)))) +
      ∑ k : Fin b, t.2 k.succ • (P k * nativeCenter (p := p)) =
      ∑ k : Fin b, (P k * QA t k + Mm k * QC t k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => e k
  rw [add_right_comm, hsum, mul_smul_comm]

end
end CatalanMeasure.GenD.Uniform.W.Charts4
