module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar.Assemble
@[expose] public section
set_option Elab.async false

/-!
# Theorem L*: `lstarKap ≤ nullity` (lane G6c)
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Tier3
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

open Classical in
/-- Reference digit of the residue `ℓ`. -/
def j0of (P : Parameters) (N p ℓ : ℕ) : ℕ :=
  if h : (jSet P N p ℓ).Nonempty then (jSet P N p ℓ).min' h else 0

theorem j0of_mem {ℓ : ℕ} (h : (jSet P N p ℓ).Nonempty) : j0of P N p ℓ ∈ jSet P N p ℓ := by
  classical
  unfold j0of
  rw [dif_pos h]
  exact Finset.min'_mem _ _

/-- Generic: the J-flatness map has rank at most `|Jset| - 1`. -/
theorem flatPhi_rank_le_card {A : Type*} [AddCommGroup A] [Module (ZMod p) A]
    (ι : A →ₗ[ZMod p] (Fin (P.n N) → ZMod p)) (Jset : ZMod p → Finset ℕ) (J0 : ZMod p → ℕ)
    (ℓ : ZMod p) (h0 : (Jset ℓ).Nonempty → J0 ℓ ∈ Jset ℓ) :
    finrank (ZMod p) (LinearMap.range (flatPhi (P := P) (N := N) ι Jset J0 ℓ)) ≤
      (Jset ℓ).card - 1 := by
  classical
  by_cases hne : (Jset ℓ).Nonempty
  · have hm := h0 hne
    have hlt : LinearMap.range (flatPhi (P := P) (N := N) ι Jset J0 ℓ) < ⊤ := by
      refine lt_top_iff_ne_top.mpr fun htop => ?_
      have hmem : (Pi.single (⟨J0 ℓ, hm⟩ : ↥(Jset ℓ)) (1 : ZMod p) : ↥(Jset ℓ) → ZMod p) ∈
          LinearMap.range (flatPhi (P := P) (N := N) ι Jset J0 ℓ) := by
        rw [htop]; trivial
      obtain ⟨a, ha⟩ := hmem
      have := congrFun ha ⟨J0 ℓ, hm⟩
      simp [flatPhi] at this
    have := Submodule.finrank_lt hlt.ne
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
    omega
  · have hz : (Jset ℓ).card = 0 := by simp [Finset.not_nonempty_iff_eq_empty.mp hne]
    have := Submodule.finrank_le (LinearMap.range (flatPhi (P := P) (N := N) ι Jset J0 ℓ))
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this
    omega

theorem lrank_bound (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    (ℓ : ZMod p) :
    finrank (ZMod p) (LinearMap.range (flatPhi (P := P) (N := N) (p := p) LinearMap.id
      (fun ℓ => jSet P N p ℓ.val) (fun ℓ => j0of P N p ℓ.val) ℓ)) ≤ lrank P N p ℓ.val := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hcard := flatPhi_rank_le_card (P := P) (N := N) (p := p) LinearMap.id
    (fun ℓ => jSet P N p ℓ.val) (fun ℓ => j0of P N p ℓ.val) ℓ (fun h => j0of_mem h)
  unfold lrank
  split_ifs with hadm
  · refine le_min ?_ hcard
    obtain ⟨hph, he⟩ := hadm
    have hLH : P.L N ≤ P.H N := by simp only [Parameters.H, Parameters.C]; omega
    by_cases hne : (jSet P N p ℓ.val).Nonempty
    · refine flatPhi_rank_le hP hN hp2 hH (dh := P.h N - p) (by omega) ℓ
        (fun ℓ => jSet P N p ℓ.val) (fun ℓ => j0of P N p ℓ.val)
        (fun J hJ => ?_) ?_ he (nvSet P N p ℓ.val) ?_
      · have := (mem_jSet hp0).mp hJ
        omega
      · have := (mem_jSet hp0).mp (j0of_mem hne)
        show j0of P N p ℓ.val * p + ℓ.val < P.H N
        omega
      · intro r hr
        have hrd := blk_eq hp2 (P.g N) r.val
        have hdle := blkD_natAbs_le hp2 (P.g N) r.val
        have hpz : (0 : ℤ) < p := by exact_mod_cast hp0
        have hrn := r.isLt
        have he0 := idxRes_lt hp0 (P.H N) ℓ.val
        have hD : ((lD P N p ℓ.val : ℕ) : ℤ) = p - 1 - idxRes (P.H N) p ℓ.val + (P.h N - p : ℕ) := by
          unfold lD; push_cast [Nat.cast_sub (by omega : idxRes (P.H N) p ℓ.val ≤ p - 1)]
          rw [Nat.cast_sub (by omega : 1 ≤ p)]; push_cast; ring
        unfold nvSet
        rw [Finset.mem_Icc]
        set k := blkK p (P.g N) r.val
        set d := blkD p (P.g N) r.val
        have hdD : d.natAbs ≤ lD P N p ℓ.val := by unfold lD; omega
        have hdz : -(lD P N p ℓ.val : ℤ) ≤ d ∧ d ≤ lD P N p ℓ.val := by omega
        constructor
        · have h1 : -k * p ≤ (P.g N : ℤ) + lD P N p ℓ.val := by nlinarith
          have := Int.le_ediv_of_mul_le hpz h1
          linarith
        · have h1 : k * p ≤ (P.n N : ℤ) - P.g N - 1 + lD P N p ℓ.val := by nlinarith
          exact Int.le_ediv_of_mul_le hpz h1
    · have hz : (jSet P N p ℓ.val).card = 0 := by simp [Finset.not_nonempty_iff_eq_empty.mp hne]
      omega
  · exact hcard

/-- **Theorem L\*.**  `lstarKap ≤ ν` for every admissible design, odd prime `p` with `H < p²`. -/
theorem lstarKap_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) :
    lstarKap P N p ≤ nullity P N p := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hq : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
  have hJ : ∀ j, P.b N ≤ j → j < P.L N →
      j / p ∈ (fun ℓ : ZMod p => jSet P N p ℓ.val) (j : ZMod p) := by
    intro j h1 h2
    show j / p ∈ jSet P N p (j : ZMod p).val
    rw [ZMod.val_natCast, mem_jSet hp0, Nat.div_add_mod' j p]
    exact ⟨h1, h2⟩
  have h := w_flatrank hp2 hH hq (A := Fin (P.n N) → ZMod p) LinearMap.id
    (fun _ _ h => h) (fun ℓ : ZMod p => jSet P N p ℓ.val) (fun ℓ => j0of P N p ℓ.val) hJ
    (fun ℓ => lrank P N p ℓ.val) (fun ℓ => lrank_bound hP hN hp2 hH ℓ)
  rw [Module.finrank_fin_fun, sum_zmod_val p (fun i => lrank P N p i)] at h
  unfold lstarKap
  exact h

#print axioms lstarKap_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.LStar
