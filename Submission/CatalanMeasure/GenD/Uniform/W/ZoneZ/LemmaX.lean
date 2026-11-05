module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.TpPlain
public import Submission.CatalanMeasure.GenD.Uniform.Prefix.ChebyshevAdd
@[expose] public section
set_option Elab.async false

/-!
# Lemma X, polynomial core (the "z-picture" as row vectors)

For a finitely supported row vector `c : ℤ →₀ F_p` set `Tl c = Σ c_m T_m`, `Ul c = Σ c_m U_{m-1}`
and let `Δ c_m = c_{m-1} + c_{m+1} - 2 c_m`.  Then `(2X-2) Tl c = Tl (Δ c)` and
`(2X-2) Ul c = Ul (Δ c)`.  With `w = U_{p-1}` and `w T_d = X^p U_{d-1} + U_{p-d-1}`,

    hi (w · (2X-2)^h Tl c) + (2X-2)^h Ul c = 2 Σ_{m>0} (Δ^h c)_m U_{m-1},

so if `c_m = 0` for `m > r` the left side has degree `< h + r`.  This is the content of zone2
Lemma X (virtual rows of the top block => deg Q_top <= h + rtop - 1), without Laurent series.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Polynomial Polynomial.Chebyshev
noncomputable section
variable {p : ℕ} [Fact p.Prime]

/-- `Σ c_m T_m`. -/
def Tl : (ℤ →₀ ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  Finsupp.lsum (ZMod p) fun m => LinearMap.toSpanSingleton (ZMod p) (ZMod p)[X] (Chebyshev.T (ZMod p) m)

/-- `Σ c_m U_{m-1}`. -/
def Ul : (ℤ →₀ ZMod p) →ₗ[ZMod p] (ZMod p)[X] :=
  Finsupp.lsum (ZMod p) fun m =>
    LinearMap.toSpanSingleton (ZMod p) (ZMod p)[X] (Chebyshev.U (ZMod p) (m - 1))

/-- The second difference `Δ c_m = c_{m-1} + c_{m+1} - 2 c_m`. -/
def Dl : (ℤ →₀ ZMod p) →ₗ[ZMod p] (ℤ →₀ ZMod p) :=
  Finsupp.lmapDomain (ZMod p) (ZMod p) (· + 1) + Finsupp.lmapDomain (ZMod p) (ZMod p) (· - 1) -
    (2 : ZMod p) • LinearMap.id

theorem Tl_single (m : ℤ) (a : ZMod p) : Tl (Finsupp.single m a) = a • Chebyshev.T (ZMod p) m := by
  simp [Tl]

theorem Ul_single (m : ℤ) (a : ZMod p) :
    Ul (Finsupp.single m a) = a • Chebyshev.U (ZMod p) (m - 1) := by
  simp [Ul]

theorem Dl_single (m : ℤ) (a : ZMod p) :
    Dl (Finsupp.single m a) = Finsupp.single (m + 1) a + Finsupp.single (m - 1) a -
      (2 : ZMod p) • Finsupp.single m a := by
  simp [Dl, Finsupp.mapDomain_single]

theorem Dl_apply (c : ℤ →₀ ZMod p) (m : ℤ) : Dl c m = c (m - 1) + c (m + 1) - 2 * c m := by
  have h1 : ∀ s : ℤ, (Finsupp.mapDomain (· + s) c) m = c (m - s) := by
    intro s
    have : Function.Injective (fun x : ℤ => x + s) := add_left_injective s
    have := Finsupp.mapDomain_apply_of_injective this c (m - s)
    simpa using this
  have h2 : ∀ s : ℤ, (Finsupp.mapDomain (· - s) c) m = c (m + s) := by
    intro s
    have : Function.Injective (fun x : ℤ => x - s) := sub_left_injective
    have := Finsupp.mapDomain_apply_of_injective this c (m + s)
    simpa using this
  simp only [Dl, LinearMap.sub_apply, LinearMap.add_apply, Finsupp.lmapDomain_apply,
    LinearMap.smul_apply, LinearMap.id_apply, Finsupp.coe_sub, Finsupp.coe_add, Pi.sub_apply,
    Pi.add_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [h1 1, h2 1]

theorem Tl_Dl (c : ℤ →₀ ZMod p) : (2 * X - 2 : (ZMod p)[X]) * Tl c = Tl (Dl c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, mul_add, hf, hg, map_add, map_add]
  | single m a =>
    rw [Dl_single, map_sub, map_add, map_smul, Tl_single, Tl_single, Tl_single]
    have h1 := Chebyshev.T_add_two (ZMod p) (m - 1)
    have e1 : (m - 1 + 2 : ℤ) = m + 1 := by ring
    have e2 : (m - 1 + 1 : ℤ) = m := by ring
    rw [e1, e2] at h1
    simp only [smul_eq_C_mul, h1]
    simp only [map_ofNat]
    ring

theorem Ul_Dl (c : ℤ →₀ ZMod p) : (2 * X - 2 : (ZMod p)[X]) * Ul c = Ul (Dl c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, mul_add, hf, hg, map_add, map_add]
  | single m a =>
    rw [Dl_single, map_sub, map_add, map_smul, Ul_single, Ul_single, Ul_single]
    have h1 := Chebyshev.U_add_two (ZMod p) (m - 2)
    have e1 : (m - 2 + 2 : ℤ) = m := by ring
    have e2 : (m - 2 + 1 : ℤ) = m - 1 := by ring
    rw [e1, e2] at h1
    have e3 : (m + 1 - 1 : ℤ) = m := by ring
    have e4 : (m - 1 - 1 : ℤ) = m - 2 := by ring
    rw [e3, e4]
    simp only [smul_eq_C_mul, h1]
    simp only [map_ofNat]
    ring

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
