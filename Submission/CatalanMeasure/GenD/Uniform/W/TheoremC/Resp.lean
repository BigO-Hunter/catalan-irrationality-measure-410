module
public import Submission.CatalanMeasure.GenD.Uniform.W.Thin.TKill
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Column
public import Submission.CatalanMeasure.GenD.Uniform.W.TheoremC.UBasis
@[expose] public section
set_option Elab.async false

/-!
# Response of a tensor `T-` family (Theorem C and C')

Pair coordinates `x_{d,k} = w_d z_k` (a fixed block profile `z` times a coordinate vector `w` of the
polynomial `σ = Σ_d w_d U_d`).  If `(X-1)^h σ = (X^p - 1) G` with `G` supported below `hi ≤ p`, the raw
residue response at `j` is

    uResp j = 2 G[e0] (ψ(a0 - 1) - ψ(a0)),   e0 = idxRes, a0 = idxQuo,  ψ(a) = psiLin (j/p) a z

(positions `e0` and `e0 + p`, windows `a0` and `a0 - 1`).
-/

namespace CatalanMeasure.GenD.Uniform.W.TheoremC
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- Pure tensor profile `x_{d,k} = w_d z_k`. -/
def tensorX {K D : ℕ} (w : Fin D → ZMod p) (z : Fin K → ZMod p) : Fin D → Fin K → ZMod p :=
  fun d k => w d * z k

theorem lam_comb {D : ℕ} (w : Fin D → ZMod p) :
    2 * (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D w =
      ∑ d : Fin D, C (w d) * lam P N p (d : ℕ) := by
  rw [uComb_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  unfold lam
  ring

theorem wvec_tensor {K D : ℕ} (w : Fin D → ZMod p) (z : Fin K → ZMod p) (e : ℕ) :
    wvec P N p (tensorX w z) e =
      ((2 * (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D w).coeff e) • z := by
  funext k
  simp only [wvec, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, tensorX, lamc]
  rw [lam_comb, Polynomial.finset_sum_coeff]
  simp only [coeff_C_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun d _ => by ring

theorem not_dvd_of_ne {u v : ℕ} (hu : u < p) (hv : v < p) (huv : u ≠ v) (a : ℤ) :
    ¬ (p : ℤ) ∣ ((u : ℤ) + p * a) - v := by
  rintro ⟨t, ht⟩
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have h1 : (t - a) * p = (u : ℤ) - v := by linarith
  have := Thin.no_mult (t - a) ((u : ℤ) - v) hp0 (by omega) (by omega) h1
  omega

theorem sum_tTerm (ψ : ℤ → ZMod p) (G : (ZMod p)[X]) (hi : ℕ) (hhi : hi ≤ p)
    (hsupp : ∀ e, G.coeff e ≠ 0 → e < hi) (X0 : ℤ) (e0 : ℕ) (a0 : ℤ) (he0 : e0 < p)
    (hX0 : X0 = e0 + p * a0) :
    ∑ e' ∈ Finset.range (p + hi),
        (if (p : ℤ) ∣ X0 - e' then
          2 * ((if p ≤ e' then G.coeff (e' - p) else 0) - G.coeff e') * ψ ((X0 - e') / p)
        else 0) = 2 * G.coeff e0 * (ψ (a0 - 1) - ψ a0) := by
  have hp0 : (0 : ℤ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpn : 0 < p := (Fact.out : p.Prime).pos
  rw [Finset.sum_range_add]
  have hG : ∀ e, hi ≤ e → G.coeff e = 0 := fun e he => by
    by_contra h
    exact absurd (hsupp e h) (by omega)
  have h1 : ∑ e' ∈ Finset.range p,
      (if (p : ℤ) ∣ X0 - e' then
        2 * ((if p ≤ e' then G.coeff (e' - p) else 0) - G.coeff e') * ψ ((X0 - e') / p)
      else 0) = -(2 * G.coeff e0 * ψ a0) := by
    rw [Finset.sum_eq_single e0]
    · have hd : (p : ℤ) ∣ X0 - e0 := ⟨a0, by rw [hX0]; ring⟩
      have hq : (X0 - e0) / p = a0 := by
        rw [hX0]
        have : (e0 : ℤ) + p * a0 - e0 = p * a0 := by ring
        rw [this]
        exact Int.mul_ediv_cancel_left _ (by omega)
      rw [if_pos hd, hq, if_neg (by omega)]
      ring
    · intro e' he' hne
      rw [if_neg]
      rw [hX0]
      have := not_dvd_of_ne (p := p) (u := e0) (v := e') he0 (Finset.mem_range.mp he') (Ne.symm hne) a0
      exact this
    · intro h
      exact absurd (Finset.mem_range.mpr he0) h
  have h2 : ∑ i ∈ Finset.range hi,
      (if (p : ℤ) ∣ X0 - ((p + i : ℕ) : ℤ) then
        2 * ((if p ≤ p + i then G.coeff (p + i - p) else 0) - G.coeff (p + i)) *
          ψ ((X0 - ((p + i : ℕ) : ℤ)) / p)
      else 0) = 2 * G.coeff e0 * ψ (a0 - 1) := by
    by_cases hlt : e0 < hi
    · rw [Finset.sum_eq_single e0]
      · have hd : (p : ℤ) ∣ X0 - ((p + e0 : ℕ) : ℤ) := ⟨a0 - 1, by push_cast; rw [hX0]; ring⟩
        have hq : (X0 - ((p + e0 : ℕ) : ℤ)) / p = a0 - 1 := by
          have : X0 - ((p + e0 : ℕ) : ℤ) = p * (a0 - 1) := by push_cast; rw [hX0]; ring
          rw [this]
          exact Int.mul_ediv_cancel_left _ (by omega)
        rw [if_pos hd, hq, if_pos (by omega), show p + e0 - p = e0 by omega,
          hG (p + e0) (by omega)]
        ring
      · intro i hi' hne
        rw [if_neg]
        have hi'' := Finset.mem_range.mp hi'
        have : X0 - ((p + i : ℕ) : ℤ) = ((e0 : ℤ) + p * (a0 - 1)) - i := by
          push_cast; rw [hX0]; ring
        rw [this]
        exact not_dvd_of_ne (p := p) (u := e0) (v := i) he0 (by omega) (Ne.symm hne) (a0 - 1)
      · intro h
        exact absurd (Finset.mem_range.mpr hlt) h
    · have hz : G.coeff e0 = 0 := hG e0 (by omega)
      rw [hz]
      simp only [mul_zero, zero_mul]
      refine Finset.sum_eq_zero fun i hi' => ?_
      have hi'' := Finset.mem_range.mp hi'
      rw [if_neg]
      have : X0 - ((p + i : ℕ) : ℤ) = ((e0 : ℤ) + p * (a0 - 1)) - i := by
        push_cast; rw [hX0]; ring
      rw [this]
      exact not_dvd_of_ne (p := p) (u := e0) (v := i) he0 (by omega) (by omega) (a0 - 1)
  rw [h1, h2]
  ring

#print axioms sum_tTerm

/-- **Response of a tensor family.** -/
theorem uResp_tensor (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {K D : ℕ} (k0 : ℤ) (z : Fin K → ZMod p) (w : Fin D → ZMod p) (G : (ZMod p)[X]) (hi : ℕ)
    (hrel : (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D w = (X ^ p - 1) * G)
    (hsupp : ∀ e, G.coeff e ≠ 0 → e < hi) (hhi : hi ≤ p) (hD : p + hi ≤ P.h N + D)
    (hx : ∀ d k, ¬ Good P N p k0 d k → tensorX w z d k = 0) {j : ℕ} (hj : j < P.H N) :
    uResp P N p j (tRows P N p K D k0 (tensorX w z)) =
      2 * G.coeff (idxRes (P.H N) p (j % p)) *
        (psiLin p K k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p) - 1) z -
          psiLin p K k0 (P.H N) (j / p) (idxQuo (P.H N) p (j % p)) z) := by
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  rw [uResp_tRows hP hN hp2 hH k0 _ hx hj]
  have hc : ∀ e', (2 * (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D w).coeff e' =
      2 * ((if p ≤ e' then G.coeff (e' - p) else 0) - G.coeff e') := by
    intro e'
    have : 2 * (X - 1 : (ZMod p)[X]) ^ P.h N * uComb p D w = C 2 * ((X ^ p - 1) * G) := by
      rw [← hrel, mul_assoc, C_ofNat]
    rw [this, coeff_C_mul, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']
  have hG : ∀ e, hi ≤ e → G.coeff e = 0 := fun e he => by
    by_contra h
    exact absurd (hsupp e h) (by omega)
  have hsum : ∑ e ∈ Finset.range (P.h N + D),
        (if (p : ℤ) ∣ (P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e then
          psiLin p K k0 (P.H N) (j / p) (((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ) - e) / p)
            (wvec P N p (tensorX w z) e)
        else 0) =
      ∑ e ∈ Finset.range (p + hi),
        (if (p : ℤ) ∣ ((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ)) - e then
          2 * ((if p ≤ e then G.coeff (e - p) else 0) - G.coeff e) *
            psiLin p K k0 (P.H N) (j / p) ((((P.H N : ℤ) - 1 - ((j % p : ℕ) : ℤ)) - e) / p) z
        else 0) := by
    have hsub : Finset.range (p + hi) ⊆ Finset.range (P.h N + D) :=
      Finset.range_subset_range.mpr hD
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun e _ => ?_
      rw [wvec_tensor, hc, map_smul, smul_eq_mul]
    · intro e _ hne
      have hne' : p + hi ≤ e := by
        by_contra h; exact hne (Finset.mem_range.mpr (by omega))
      rw [wvec_tensor, hc, hG e (by omega)]
      have : (if p ≤ e then G.coeff (e - p) else 0) = 0 := by
        rw [if_pos (by omega)]; exact hG _ (by omega)
      rw [this]
      simp
  rw [hsum]
  have hidx := idx_eq hp0 (P.H N) (j % p)
  have hres := idxRes_lt hp0 (P.H N) (j % p)
  exact sum_tTerm (fun a => psiLin p K k0 (P.H N) (j / p) a z) G hi hhi hsupp _
    (idxRes (P.H N) p (j % p)) (idxQuo (P.H N) p (j % p)) hres hidx

#print axioms uResp_tensor
end
end CatalanMeasure.GenD.Uniform.W.TheoremC
