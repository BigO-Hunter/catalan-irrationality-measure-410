module
public import Submission.CatalanMeasure.GenD.Uniform.W.FrobInst.Coords
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.TRaw
public import Submission.CatalanMeasure.GenD.Uniform.W.Frob.Product
@[expose] public section
set_option Elab.async false

/-!
# Frobenius-product atoms (C type) and the instance `FrobProductData`

KERNEL-FAMILY-THEOREM (F0-F4).  The atom of a profile tensor `x : Π ⊗ F_p^K`
(`Π = F_p^{dP+1}` coordinates of `P(y) = Σ_j P_j y^j`, `F_p^K` the `τ`-window
`Λ = Σ_k λ_k τ^{k0+k}`) is the Laurent polynomial `Δ · y^lo · P(y) · Λ(t^p)`, up to the
constant `2`:

    c(x) = Σ_{k} t^{(k0+k)p} · Σ_d u_{d,k} (t^{d+1} - t^{-(d+1)}),
    t^m - t^{-m} = 2 Δ U_{m-1}(y),   Σ_d u_{d,k} U_d = y^lo P_k(y),   u = prof x.

* `prof` : the `y^{lo+j} ↦ U`-coordinates change (`Coords`), injective;
* `cTheta = tRows ∘ prof` is the atom map on all of `Π ⊗ F_p^K`;
* `seenSet` : the F3 set of seen `(J, s)` pairs, a closed floor/residue image of the active
  window; `hseen` is then automatic;
* `frobData` : the structure `FrobProductData`, with `inj` from `tRows_injective_on` (F4) and
  `killed` from `uResp_tRows_eq_zero` (F3).  Only the window inequalities remain.
-/

namespace CatalanMeasure.GenD.Uniform.W.FrobInst
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W.Thin
  CatalanMeasure.GenD.Uniform.W
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- The change of coordinates `P ↦ y^lo P` into the `U`-basis, on profile tensors. -/
def prof (hp2 : p ≠ 2) (K lo m : ℕ) :
    (Fin m → Fin K → ZMod p) →ₗ[ZMod p] (Fin (lo + m) → Fin K → ZMod p) where
  toFun x d k := ∑ j : Fin m, ucoef hp2 (lo + m) (lo + j) d * x j k
  map_add' x y := by
    ext d k
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    ext d k
    simp [Finset.mul_sum, mul_left_comm]

theorem prof_apply (hp2 : p ≠ 2) (K lo m : ℕ) (x : Fin m → Fin K → ZMod p)
    (d : Fin (lo + m)) (k : Fin K) :
    prof hp2 K lo m x d k = ∑ j : Fin m, ucoef hp2 (lo + m) (lo + j) d * x j k := rfl

theorem prof_injective (hp2 : p ≠ 2) (K lo m : ℕ) : Function.Injective (prof hp2 K lo m) := by
  refine injective_of_zero _ fun x hx => ?_
  funext j k
  have hk : ∀ k : Fin K, ∑ j : Fin m, C (x j k) * (X : (ZMod p)[X]) ^ (lo + (j : ℕ)) = 0 := by
    intro k
    have h1 : ∀ j : Fin m, (X : (ZMod p)[X]) ^ (lo + (j : ℕ)) =
        ∑ d : Fin (lo + m), C (ucoef hp2 (lo + m) (lo + j) d) *
          Chebyshev.U (ZMod p) ((d : ℕ) : ℤ) := fun j =>
      (ucoef_spec hp2 (lo + m) (lo + j) (by have := j.isLt; omega)).symm
    simp_rw [h1, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun d _ => ?_
    have h2 : ∑ j : Fin m, ucoef hp2 (lo + m) (lo + j) d * x j k = 0 :=
      congrFun (congrFun hx d) k
    have h3 : ∑ j : Fin m, C (x j k) * (C (ucoef hp2 (lo + m) (lo + j) d) *
        Chebyshev.U (ZMod p) ((d : ℕ) : ℤ)) =
        C (∑ j : Fin m, ucoef hp2 (lo + m) (lo + j) d * x j k) *
          Chebyshev.U (ZMod p) ((d : ℕ) : ℤ) := by
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul]; ring
    rw [h3, h2]; simp
  have hc := congrArg (fun q : (ZMod p)[X] => q.coeff (lo + (j : ℕ))) (hk k)
  simp only [finsetSum_coeff, coeff_C_mul, coeff_X_pow, coeff_zero] at hc
  rw [Finset.sum_eq_single j] at hc
  · simpa using hc
  · intro j' _ hj'
    have h' : (j : ℕ) ≠ (j' : ℕ) := fun h => hj' (Fin.ext h.symm)
    simp [h']
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The atom map of the Frobenius-product family `Δ y^lo P(y) Λ(τ)` on `Π ⊗ F_p^K`. -/
def cTheta (P : Parameters) (N p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (K lo m : ℕ) (k0 : ℤ) :
    (Fin m → Fin K → ZMod p) →ₗ[ZMod p] (Fin (P.n N) → ZMod p) :=
  (tRows P N p K (lo + m) k0).comp (prof hp2 K lo m)

/-- Slot coefficients of an atom: `w_e = Σ_j [X^e] (2 (X-1)^h X^{lo+j}) · x_j`. -/
theorem wvec_prof (hp2 : p ≠ 2) {K lo m : ℕ} (x : Fin m → Fin K → ZMod p) (e : ℕ) :
    wvec P N p (prof hp2 K lo m x) e =
      ∑ j : Fin m, (2 * (X - 1) ^ P.h N * X ^ (lo + (j : ℕ)) : (ZMod p)[X]).coeff e • x j := by
  funext k
  simp only [wvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, prof_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ucoef_lamc (P := P) (N := N) hp2 (lo + m) (lo + (j : ℕ)) e (by have := j.isLt; omega),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  ring

theorem wvec_prof_low (hp2 : p ≠ 2) {K lo m : ℕ} (x : Fin m → Fin K → ZMod p) (e : ℕ)
    (he : e < lo) : wvec P N p (prof hp2 K lo m x) e = 0 := by
  rw [wvec_prof]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [coeff_lam_mono_low e (lo + j) _ (by omega)]
  simp

/-- The set of seen pairs `(J, a)` (F3): the active columns `j ∈ [b, L)` and slot exponents
`e ∈ [lo, h + D)` with `p ∣ H - 1 - (j mod p) - e`, recorded as `(j / p, (H-1-(j mod p)-e)/p)`. -/
def seenSet (P : Parameters) (N p lo D : ℕ) : Finset (ℕ × ℤ) :=
  (((Finset.Ico (P.b N) (P.L N)) ×ˢ (Finset.Ico lo (P.h N + D))).filter
    (fun je : ℕ × ℕ => (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((je.1 % p : ℕ) : ℤ) - je.2)).image
    (fun je => (je.1 / p, ((P.H N : ℤ) - 1 - ((je.1 % p : ℕ) : ℤ) - je.2) / p))

theorem seenSet_spec (lo D : ℕ) :
    ∀ j e (a : ℤ), P.b N ≤ j → j < P.L N → lo ≤ e → e < P.h N + D →
      (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e = a * p → (j / p, a) ∈ seenSet P N p lo D := by
  intro j e a h1 h2 h3 h4 h5
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold seenSet
  refine Finset.mem_image.mpr ⟨(j, e), ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_Ico.mpr ⟨h1, h2⟩,
      Finset.mem_Ico.mpr ⟨h3, h4⟩⟩, ?_⟩
    simp only
    rw [h5]; exact dvd_mul_left _ _
  · simp only
    rw [h5, Int.mul_ediv_cancel _ hp0]

/-- Window conditions of the C-type family: all products are actual rows (F4). -/
def FrobGood (P : Parameters) (N p K lo m : ℕ) (k0 : ℤ) : Prop :=
  ∀ k : ℕ, k < K → -(P.g N : ℤ) + ((lo + m : ℕ) : ℤ) ≤ (k0 + k) * p ∧
    (k0 + k) * p + ((lo + m : ℕ) : ℤ) < (P.n N : ℤ) - P.g N

theorem frobGood_good {K lo m : ℕ} {k0 : ℤ} (h : FrobGood P N p K lo m k0)
    (d : Fin (lo + m)) (k : Fin K) : Good P N p k0 d k := by
  obtain ⟨h1, h2⟩ := h k k.isLt
  have hd := d.isLt
  unfold Good InRange cen
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> push_cast at * <;> omega

/-- **The instance.**  `m = dP + 1`, `β = K`, `e = #seen`, `E` the seen functionals. -/
def frobData (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K lo dP : ℕ} {k0 : ℤ} (hD : lo + (dP + 1) ≤ (p - 1) / 2)
    (hg : FrobGood P N p K lo (dP + 1) k0) : FrobProductData P N p where
  m := dP + 1
  β := K
  e := (seenSet P N p lo (lo + (dP + 1))).card
  E := seenMap p K k0 (P.H N) (seenSet P N p lo (lo + (dP + 1)))
  Θ := cTheta P N p hp2 K lo (dP + 1) k0
  inj := by
    refine injective_of_zero _ fun x hx => ?_
    have h0 : prof hp2 K lo (dP + 1) x = 0 :=
      tRows_injective_on (P := P) (N := N) hp2 hD k0 _
        (fun d k hgd => absurd (frobGood_good hg d k) hgd) hx
    exact prof_injective hp2 K lo (dP + 1) (by rw [h0, map_zero])
  killed := by
    intro x hx
    have hq : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
    have hjH : ∀ j, j < P.L N → j < P.H N := by
      intro j hj
      have := hP.2.2.2.1
      have h2 : 0 < P.h N := Nat.mul_pos this hN
      simp only [Parameters.H, Parameters.C]
      omega
    refine ⟨0, by simpa using hq, fun j h1 h2 => ?_⟩
    rw [Polynomial.eval_zero]
    refine uResp_tRows_eq_zero hP hN hp2 hH k0 (prof hp2 K lo (dP + 1) x)
      (fun d k hgd => absurd (frobGood_good hg d k) hgd) (hjH j h2) ?_
    intro e he a hea
    by_cases hlt : e < lo
    · rw [wvec_prof_low hp2 x e hlt]; simp
    · have hmem := seenSet_spec (P := P) (N := N) (p := p) lo (lo + (dP + 1)) j e a h1 h2
        (not_lt.mp hlt) he hea
      rw [wvec_prof]
      simp only [map_sum, map_smul, smul_eq_mul]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [seenMap_apply_mem K k0 _ _ (x i) ?_ _ _ hmem, mul_zero]
      exact LinearMap.mem_ker.mpr (hx i)

end
end CatalanMeasure.GenD.Uniform.W.FrobInst
