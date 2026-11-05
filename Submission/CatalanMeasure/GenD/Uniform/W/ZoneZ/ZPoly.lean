module
public import Submission.CatalanMeasure.GenD.Uniform.W.ZoneZ.ZAtom
@[expose] public section
set_option Elab.async false

/-!
# The slot polynomials of a Theorem Z atom: degrees, fold, valuations

`Pi_poly τ = Σ τ_d zpLam_d = 2 (X-1)^h w tpoly τ` (`w = (X²-1)^hp`), `La_poly σ = 2 (X-1)^h upoly σ`.

* `piSeq_hi_zero`, `laSeq_hi_zero`: degree bounds (`π[e] = 0` for `e ≥ h+p+hp`, `λ[e] = 0` for `e ≥ h+hp`);
* `fold2`: if `(X-1)^{hp+1-h} ∣ tpoly τ2` then `Pi_poly τ2 = (X^p - 1) P2`: `π2[r] + π2[r+p] = 0`
  and `π2[r] = π2[r+p] = 0` for `h+hp ≤ r < p`;
* `val1`: if `(X-1)^{hp+1-h-q} ∣ tpoly τ1` then `(X-1)^{p-q} ∣ Pi_poly τ1`.
-/

namespace CatalanMeasure.GenD.Uniform.W.ZoneZ
open Module Polynomial Polynomial.Chebyshev CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
  CatalanMeasure.GenD.Uniform.W.SlotsT
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `Σ τ_d T_d`. -/
def tpoly {D : ℕ} (τ : Fin D → ZMod p) : (ZMod p)[X] :=
  ∑ d : Fin D, C (τ d) * Chebyshev.T (ZMod p) ((d : ℕ) : ℤ)

/-- `Σ σ_d U_{d-1}`. -/
def upoly {D : ℕ} (σ : Fin D → ZMod p) : (ZMod p)[X] :=
  ∑ d : Fin D, C (σ d) * Chebyshev.U (ZMod p) (((d : ℕ) : ℤ) - 1)

def Pi_poly (P : Parameters) (N p : ℕ) [Fact p.Prime] {D : ℕ} (τ : Fin D → ZMod p) : (ZMod p)[X] :=
  ∑ d : Fin D, C (τ d) * zpLam P N p d

def La_poly (P : Parameters) (N p : ℕ) [Fact p.Prime] {D : ℕ} (σ : Fin D → ZMod p) : (ZMod p)[X] :=
  ∑ d : Fin D, C (σ d) * zaLam P N p d

theorem piSeq_eq {D : ℕ} (τ : Fin D → ZMod p) (e : ℕ) :
    piSeq P N p τ e = (Pi_poly P N p τ).coeff e := by
  simp only [piSeq, Pi_poly, finsetSum_coeff, coeff_C_mul]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

theorem laSeq_eq {D : ℕ} (σ : Fin D → ZMod p) (e : ℕ) :
    laSeq P N p σ e = (La_poly P N p σ).coeff e := by
  simp only [laSeq, La_poly, finsetSum_coeff, coeff_C_mul]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

theorem Pi_poly_eq {D : ℕ} (τ : Fin D → ZMod p) :
    Pi_poly P N p τ = 2 * (X - 1) ^ P.h N * (X ^ 2 - 1) ^ ((p - 1) / 2) * tpoly τ := by
  simp only [Pi_poly, tpoly, zpLam, Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

theorem La_poly_eq {D : ℕ} (σ : Fin D → ZMod p) :
    La_poly P N p σ = 2 * (X - 1) ^ P.h N * upoly σ := by
  simp only [La_poly, upoly, zaLam, Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

/-- `zaLam d` has degree `< h + d` (and is `0` for `d = 0`). -/
theorem zaLam_coeff_zero (hp2 : p ≠ 2) (d e : ℕ) (he : P.h N + d ≤ e) :
    (zaLam P N p d).coeff e = 0 := by
  haveI : NeZero (2 : ZMod p) := ⟨two_ne_zero_zmod hp2⟩
  rcases d with _ | d
  · simp [zaLam]
  · apply coeff_eq_zero_of_natDegree_lt
    unfold zaLam
    have h1 : (2 * (X - 1) ^ P.h N : (ZMod p)[X]).natDegree ≤ P.h N := by
      refine natDegree_mul_le.trans ?_
      have a : (2 : (ZMod p)[X]).natDegree ≤ 0 := by compute_degree
      have b : ((X - 1) ^ P.h N : (ZMod p)[X]).natDegree ≤ P.h N := by
        refine natDegree_pow_le.trans ?_
        have : (X - 1 : (ZMod p)[X]).natDegree ≤ 1 := by compute_degree
        nlinarith
      omega
    have h2 : (Chebyshev.U (ZMod p) (((d + 1 : ℕ) : ℤ) - 1)).natDegree = d := by
      have : (((d + 1 : ℕ) : ℤ) - 1) = (d : ℤ) := by push_cast; ring
      rw [this, Chebyshev.natDegree_U_natCast]
    have := natDegree_mul_le (p := (2 * (X - 1) ^ P.h N : (ZMod p)[X]))
      (q := Chebyshev.U (ZMod p) (((d + 1 : ℕ) : ℤ) - 1))
    omega

theorem laSeq_hi_zero (hp2 : p ≠ 2) {hp : ℕ} (σ : Fin (hp + 1) → ZMod p) (e : ℕ)
    (he : P.h N + hp ≤ e) : laSeq P N p σ e = 0 := by
  unfold laSeq
  refine Finset.sum_eq_zero fun d _ => ?_
  have := d.isLt
  rw [zaLam_coeff_zero hp2 d e (by omega), zero_mul]

theorem piSeq_hi_zero (hp2 : p ≠ 2) {hp : ℕ} (τ : Fin (hp + 1) → ZMod p) (e : ℕ)
    (he : P.h N + (p - 1) + hp < e) : piSeq P N p τ e = 0 := by
  unfold piSeq
  refine Finset.sum_eq_zero fun d _ => ?_
  have := d.isLt
  have h1 := zpLam_natDegree_le (P := P) (N := N) hp2 (d : ℕ)
  rw [coeff_eq_zero_of_natDegree_lt (by omega), zero_mul]

/-- **Valuation transfer**: `(X-1)^e ∣ tpoly τ` gives `(X-1)^{h+hp+e} ∣ Pi_poly τ`. -/
theorem val_Pi {D : ℕ} (τ : Fin D → ZMod p) (e : ℕ) (hdv : ((X - 1) ^ e : (ZMod p)[X]) ∣ tpoly τ) :
    ((X - 1) ^ (P.h N + (p - 1) / 2 + e) : (ZMod p)[X]) ∣ Pi_poly P N p τ := by
  rw [Pi_poly_eq]
  obtain ⟨R, hR⟩ := hdv
  refine ⟨2 * (X + 1) ^ ((p - 1) / 2) * R, ?_⟩
  have e1 : (X ^ 2 - 1 : (ZMod p)[X]) = (X - 1) * (X + 1) := by ring
  rw [hR, e1, mul_pow, pow_add, pow_add]
  ring

/-- **Fold of the period slot**: `(X-1)^p ∣ π2` forces `π2[r] + π2[r+p] = 0` for `r < p` and
`π2[r] = π2[r+p] = 0` for `h + hp ≤ r < p`. -/
theorem fold2 (hp2 : p ≠ 2) {hp : ℕ} (hphp : hp = (p - 1) / 2) (hhp : P.h N + hp ≤ p - 1)
    (τ : Fin (hp + 1) → ZMod p) (e : ℕ) (hdv : ((X - 1) ^ e : (ZMod p)[X]) ∣ tpoly τ)
    (he : p ≤ P.h N + (p - 1) / 2 + e) (r : ℕ) (hr : r < p) :
    piSeq P N p τ r + piSeq P N p τ (r + p) = 0 ∧
      (P.h N + hp ≤ r → piSeq P N p τ r = 0 ∧ piSeq P N p τ (r + p) = 0) := by
  have hdvd := val_Pi (P := P) (N := N) τ e hdv
  have hdvp : ((X - 1) ^ p : (ZMod p)[X]) ∣ Pi_poly P N p τ :=
    (pow_dvd_pow _ he).trans hdvd
  have hX : ((X - 1) ^ p : (ZMod p)[X]) = X ^ p - 1 := by
    rw [sub_pow_char]; simp
  rw [hX] at hdvp
  obtain ⟨P2, hP2⟩ := hdvp
  -- degree of P2
  have hdeg : ∀ i, P.h N + hp ≤ i → P2.coeff i = 0 := by
    intro i hi
    by_contra hne
    have hP2ne : P2 ≠ 0 := fun h => hne (by simp [h])
    have hle : P2.natDegree + p ≤ P.h N + (p - 1) + hp := by
      by_contra hcon
      have hc : (Pi_poly P N p τ).coeff (P2.natDegree + p) ≠ 0 := by
        rw [hP2, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul]
        rw [coeff_eq_zero_of_natDegree_lt (p := P2) (by omega : P2.natDegree < P2.natDegree + p)]
        simpa using (leadingCoeff_ne_zero.mpr hP2ne)
      have := piSeq_hi_zero (P := P) (N := N) hp2 τ (P2.natDegree + p) (by omega)
      rw [piSeq_eq] at this
      exact hc this
    have : i ≤ P2.natDegree := le_natDegree_of_ne_zero hne
    omega
  have c1 : piSeq P N p τ r = -P2.coeff r := by
    rw [piSeq_eq, hP2, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']
    rw [if_neg (by omega)]; simp
  have c2 : piSeq P N p τ (r + p) = P2.coeff r - P2.coeff (r + p) := by
    rw [piSeq_eq, hP2, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']
    rw [if_pos (by omega)]
    simp
  have c3 : P2.coeff (r + p) = 0 := hdeg _ (by omega)
  refine ⟨by rw [c1, c2, c3]; ring, fun hr2 => ⟨?_, ?_⟩⟩
  · rw [c1, hdeg r hr2]; simp
  · rw [c2, hdeg r hr2, c3]; simp

end
end CatalanMeasure.GenD.Uniform.W.ZoneZ
