module
public import Submission.CatalanMeasure.GenD.Uniform.W.LStar2.Theorem2
@[expose] public section
set_option Elab.async false

/-!
# `lstar2Kap ≤ ν` (lane G6d)
-/

namespace CatalanMeasure.GenD.Uniform.W.LStar2
open Module Polynomial CatalanMeasure.Parametric OAI.InternalCatalan CatalanMeasure.GenD
  CatalanMeasure.GenD.Uniform.W CatalanMeasure.GenD.Uniform.W.Tier3
  CatalanMeasure.GenD.Uniform.W.LStar
noncomputable section
variable {P : Parameters} {N p : ℕ} [Fact p.Prime]

theorem map_finrank_le_range (K : Submodule (ZMod p) (Fin (P.n N) → ZMod p)) (ℓ : ZMod p) :
    finrank (ZMod p) ↥(K.map (PhiL P N p ℓ)) ≤ (jSet P N p ℓ.val).card - 1 := by
  have h1 : finrank (ZMod p) ↥(K.map (PhiL P N p ℓ)) ≤
      finrank (ZMod p) ↥(LinearMap.range (PhiL P N p ℓ)) :=
    Submodule.finrank_mono (LinearMap.map_le_range)
  have h2 := flatPhi_rank_le_card (P := P) (N := N) (p := p) LinearMap.id
    (fun ℓ => jSet P N p ℓ.val) (fun ℓ => j0of P N p ℓ.val) ℓ (fun h => j0of_mem h)
  exact h1.trans h2

theorem step_bound (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2)
    {t : ℕ} (ht : t < p) :
    finrank (ZMod p) ↥((Kc P N p t).map (PhiL P N p (t : ZMod p))) ≤ lrank2 P N p t := by
  classical
  have hv : ((t : ℕ) : ZMod p).val = t := ZMod.val_cast_of_lt ht
  have hrng := map_finrank_le_range (P := P) (N := N) (p := p) (Kc P N p t) (t : ZMod p)
  have e1 : jSet P N p ((t : ℕ) : ZMod p).val = jSet P N p t := by rw [hv]
  have hrng' : finrank (ZMod p) ↥((Kc P N p t).map (PhiL P N p (t : ZMod p))) ≤
      (jSet P N p t).card - 1 := hrng.trans (le_of_eq (by rw [e1]))
  unfold lrank2
  split_ifs with hw hh
  · refine le_min ?_ hrng'
    have hsub : (Kc P N p t).map (PhiL P N p (t : ZMod p)) ≤ Submodule.span (ZMod p)
        ((((nvSet P N p (t - (p - P.h N))).image
          (Gvec P N p (t - (p - P.h N)) t) : Finset _) :
            Set (↥(jSet P N p (t : ZMod p).val) → ZMod p))) := by
      rintro _ ⟨c, hc, rfl⟩
      exact step_win hP hN hp2 hH ht hw c hc
    calc finrank (ZMod p) ↥((Kc P N p t).map (PhiL P N p (t : ZMod p)))
        ≤ finrank (ZMod p) ↥(Submodule.span (ZMod p)
            ((((nvSet P N p (t - (p - P.h N))).image
              (Gvec P N p (t - (p - P.h N)) t) : Finset _) :
                Set (↥(jSet P N p (t : ZMod p).val) → ZMod p)))) := Submodule.finrank_mono hsub
      _ ≤ ((nvSet P N p (t - (p - P.h N))).image (Gvec P N p (t - (p - P.h N)) t)).card :=
          finrank_span_finset_le_card _
      _ ≤ (nvSet P N p (t - (p - P.h N))).card := Finset.card_image_le
  · exact hrng'
  · have h1 : finrank (ZMod p) ↥((Kc P N p t).map (PhiL P N p (t : ZMod p))) ≤
        finrank (ZMod p) ↥(LinearMap.range (PhiL P N p (t : ZMod p))) :=
      Submodule.finrank_mono (LinearMap.map_le_range)
    have h2 := lrank_bound hP hN hp2 hH (t : ZMod p)
    have e2 : lrank P N p ((t : ℕ) : ZMod p).val = lrank P N p t := by rw [hv]
    exact h1.trans (h2.trans (le_of_eq e2))

/-- **Theorem L\* for all `h`.** -/
theorem lstar2Kap_le_nullity (hP : Admissible P) (hN : 0 < N) (hp2 : p ≠ 2) (hH : P.H N < p ^ 2) :
    lstar2Kap P N p ≤ nullity P N p := by
  classical
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hq : 0 < P.q N := Nat.mul_pos hP.2.2.1 hN
  have hchain : ∀ t ≤ p, P.n N ≤
      finrank (ZMod p) ↥(Kc P N p t) + ∑ i ∈ Finset.range t, lrank2 P N p i := by
    intro t
    induction t with
    | zero =>
      intro _
      show P.n N ≤ finrank (ZMod p) ↥(⊤ : Submodule (ZMod p) (Fin (P.n N) → ZMod p)) +
        ∑ i ∈ Finset.range 0, lrank2 P N p i
      rw [finrank_top, Module.finrank_fin_fun, Finset.sum_range_zero]
      omega
    | succ t ih =>
      intro ht
      have h1 := ih (by omega)
      have h2 := chain_step (Kc P N p t) (PhiL P N p (t : ZMod p))
      have h3 := step_bound hP hN hp2 hH (t := t) (by omega)
      rw [Finset.sum_range_succ]
      have h4 : finrank (ZMod p) ↥(Kc P N p (t + 1)) =
          finrank (ZMod p) ↥(Kc P N p t ⊓ LinearMap.ker (PhiL P N p (t : ZMod p))) := rfl
      omega
  have hJ : ∀ j, P.b N ≤ j → j < P.L N →
      j / p ∈ (fun ℓ : ZMod p => jSet P N p ℓ.val) (j : ZMod p) := by
    intro j h1 h2
    show j / p ∈ jSet P N p (j : ZMod p).val
    rw [ZMod.val_natCast, mem_jSet hp0, Nat.div_add_mod' j p]
    exact ⟨h1, h2⟩
  have hker : Kc P N p p ≤ LinearMap.ker (stackMap (PhiL P N p)) := by
    intro c hc
    rw [LinearMap.mem_ker, stackMap_eq_zero_iff]
    intro ℓ
    have := Kc_le_ker (P := P) (N := N) (p := p) (s := p) (t := ℓ.val) (ZMod.val_lt ℓ) hc
    rw [ZMod.natCast_zmod_val] at this
    exact LinearMap.mem_ker.mp this
  have hrk : finrank (ZMod p) ↥(LinearMap.range (stackMap (PhiL P N p))) ≤
      ∑ i ∈ Finset.range p, lrank2 P N p i := by
    have h1 := LinearMap.finrank_range_add_finrank_ker (stackMap (PhiL P N p))
    have h2 := Submodule.finrank_mono hker
    have h3 := hchain p le_rfl
    rw [Module.finrank_fin_fun] at h1
    omega
  have h := w_flatrank' hp2 hH hq (A := Fin (P.n N) → ZMod p) LinearMap.id
    (fun _ _ h => h) (fun ℓ : ZMod p => jSet P N p ℓ.val) (fun ℓ => j0of P N p ℓ.val) hJ
    (∑ i ∈ Finset.range p, lrank2 P N p i) hrk
  rw [Module.finrank_fin_fun] at h
  unfold lstar2Kap
  exact h

#print axioms lstar2Kap_le_nullity
end
end CatalanMeasure.GenD.Uniform.W.LStar2
