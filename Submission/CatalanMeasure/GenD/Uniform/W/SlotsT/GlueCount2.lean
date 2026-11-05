module
public import Submission.CatalanMeasure.GenD.Uniform.W.SlotsT.GlueCount1
@[expose] public section
set_option Elab.async false

/-!
# The overflow-below family: the folded polynomial is J-flat
-/

namespace CatalanMeasure.GenD.Uniform.W.SlotsT
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan
  CatalanMeasure.GenD.Uniform.Prefix CatalanMeasure.GenD CatalanMeasure.GenD.Uniform.W
  CatalanMeasure.GenD.Uniform.W.Thin CatalanMeasure.GenD.Uniform.W.Slots
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

/-- `f = Σ_i A_i lamPoly σ_i + B_i pPoly τ_i`. -/
def fPoly (P : Parameters) (N p : ℕ) [Fact p.Prime] {D1 m : ℕ} (A B : Fin m → ZMod p)
    (a : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) : (ZMod p)[X] :=
  ∑ i, (C (A i) * lamPoly P N p (a.1 i) + C (B i) * pPoly P N p (a.2 i))

theorem fPoly_coeff {D1 m : ℕ} (A B : Fin m → ZMod p)
    (a : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) (e : ℕ) :
    (fPoly P N p A B a).coeff e = fcoef (P := P) (N := N) A B a e := by
  simp [fPoly, fcoef, finset_sum_coeff, coeff_C_mul]

/-- Truncation to degrees `< n`. -/
def lowPoly {R : Type*} [Semiring R] (n : ℕ) (f : R[X]) : R[X] :=
  ∑ e ∈ Finset.range n, monomial e (f.coeff e)

theorem lowPoly_coeff {R : Type*} [Semiring R] (n : ℕ) (f : R[X]) (e : ℕ) :
    (lowPoly n f).coeff e = if e < n then f.coeff e else 0 := by
  classical
  simp [lowPoly, finset_sum_coeff, coeff_monomial]

theorem lowPoly_natDegree_lt {R : Type*} [Semiring R] (n : ℕ) (f : R[X]) :
    (lowPoly n f).natDegree ≤ n - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ fun e he => ?_
  have := Finset.mem_range.mp he
  exact (natDegree_monomial_le _).trans (by omega)

/-- The folded polynomial `W = f + (X^p - 1) · lowPoly_{η-p+1} f`. -/
def foldPoly (P : Parameters) (N p η : ℕ) [Fact p.Prime] {D1 m : ℕ} (A B : Fin m → ZMod p)
    (a : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) : (ZMod p)[X] :=
  fPoly P N p A B a + (X ^ p - 1) * lowPoly (η - p + 1) (fPoly P N p A B a)

set_option maxHeartbeats 800000 in
theorem fold_poly (hp2 : p ≠ 2) (hph : p ≤ P.h N + (p - 1) / 2) {D1 m η : ℕ}
    (hv : P.h N + (p - 1) / 2 - p < p) (hpη : p ≤ η) (hη2 : η < 2 * p)
    (hdeg : P.h N + D1 ≤ η + 1) (A B : Fin m → ZMod p)
    (a : (Fin m → Fin D1 → ZMod p) × (Fin m → Fin (D1 + 1) → ZMod p)) :
    ∃ G : (ZMod p)[X], G.degree < ((p - (P.h N + (p - 1) / 2 - p) : ℕ) : WithBot ℕ) ∧
      ∀ ℓ : ZMod p,
        (if ℓ.val ≤ η then fcoef (P := P) (N := N) A B a (η - ℓ.val) +
          (if p + ℓ.val ≤ η then fcoef (P := P) (N := N) A B a (η - p - ℓ.val) else 0) else 0) =
        G.eval ℓ := by
  classical
  have hpo := p_odd_half hp2
  set f := fPoly P N p A B a with hf
  set t := lowPoly (η - p + 1) f with ht
  have hfdeg : f.natDegree ≤ η := by
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_C_mul_le _ _).trans ((lamPoly_natDegree_le hp2 _).trans (by omega))
    · exact (natDegree_C_mul_le _ _).trans ((pPoly_natDegree_le hp2 hph _).trans (by omega))
  have htdeg : t.natDegree ≤ η - p := by
    have h : t.natDegree ≤ η - p + 1 - 1 := lowPoly_natDegree_lt (η - p + 1) f
    omega
  have hXp : (X ^ p - 1 : (ZMod p)[X]).natDegree = p :=
    natDegree_X_pow_sub_C (n := p) (r := (1 : ZMod p))
  have hWdeg : (foldPoly P N p η A B a).natDegree ≤ η := by
    show (f + (X ^ p - 1) * t).natDegree ≤ η
    refine (natDegree_add_le _ _).trans (max_le hfdeg ?_)
    refine natDegree_mul_le.trans ?_
    rw [hXp]; omega
  have hcoef_t : ∀ e, t.coeff e = if e < η - p + 1 then f.coeff e else 0 := fun e => lowPoly_coeff _ _ _
  have hWcoef : ∀ e, (foldPoly P N p η A B a).coeff e =
      f.coeff e + ((if p ≤ e then t.coeff (e - p) else 0) - t.coeff e) := by
    intro e
    show (f + (X ^ p - 1) * t).coeff e = _
    rw [coeff_add, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']
  have hWlo : ∀ i, i + p ≤ η → (foldPoly P N p η A B a).coeff i = 0 := by
    intro i hi
    rw [hWcoef, hcoef_t i, if_neg (by omega), if_pos (by omega)]
    simp
  have hdvd : ((X - 1) ^ (P.h N + (p - 1) / 2 - p) : (ZMod p)[X]) ∣ foldPoly P N p η A B a := by
    show _ ∣ f + (X ^ p - 1) * t
    refine dvd_add ?_ ?_
    · refine Finset.dvd_sum fun i _ => dvd_add ?_ ?_
      · refine dvd_mul_of_dvd_right ?_ _
        refine Finset.dvd_sum fun d _ => dvd_mul_of_dvd_right ?_ _
        unfold Thin.lam
        exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow _ (by omega)) _) _
      · refine dvd_mul_of_dvd_right ?_ _
        refine Finset.dvd_sum fun d _ => dvd_mul_of_dvd_right ?_ _
        exact tpLam_dvd P N p _
    · refine dvd_mul_of_dvd_left ?_ _
      rw [← sub_one_pow_prime]
      exact pow_dvd_pow _ hv.le
  obtain ⟨G, hG, hGe⟩ := jflat_poly hv _ hdvd η hWdeg hWlo
  refine ⟨G, hG, fun ℓ => ?_⟩
  rw [← hGe ℓ]
  have hlp : ℓ.val < p := ZMod.val_lt ℓ
  have hlη : ℓ.val ≤ η := by omega
  rw [if_pos hlη, if_pos hlη, hWcoef]
  by_cases hpl : p + ℓ.val ≤ η
  · rw [if_pos hpl, if_pos (by omega : p ≤ η - ℓ.val), hcoef_t (η - ℓ.val - p),
      if_pos (by omega), hcoef_t (η - ℓ.val), if_neg (by omega), sub_zero,
      show η - ℓ.val - p = η - p - ℓ.val by omega, hf, fPoly_coeff, fPoly_coeff]
  · rw [if_neg hpl, if_neg (by omega : ¬ p ≤ η - ℓ.val), hcoef_t (η - ℓ.val), if_neg (by omega),
      hf, fPoly_coeff]
    simp

end
end CatalanMeasure.GenD.Uniform.W.SlotsT
