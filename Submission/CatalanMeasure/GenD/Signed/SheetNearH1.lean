module

public import Submission.CatalanMeasure.GenD.Signed.EnergyNear
public import Submission.CatalanMeasure.GenD.Signed.MarkedExpansion
public import Submission.CatalanMeasure.GenD.Signed.RealPlaceFixed

/-!
# The marked sheet with first-kind fixed and near-type rows: transport lemmas

Bookkeeping between the determinant side (`MarkedExpansion`: the `S`-term
`exp (lamS (x ∘ σ) e (S.map inr))` on the sign-split index `Fin (k+m1) ⊕ Fin (q+m2')`) and the
energy side (`EnergyNear`: five lists `xn, yn, gp, yp, zp` with the near rows `zp = S`).

* `logRatioZ_comp_pos`: the route II ratio is invariant under a permutation of the positives;
* `sum_Tc_eq`, `sum_T_eq`: Finset sums over a subset `T` and its complement along an equivalence
  `A ⊕ B ≃ ι` with `inl ↦ Tᶜ`, `inr ↦ T`;
* `lamS_transport`: `lamS u e T` as the three energy sums of the lists;
* `exists_split_finset`, `near_split_data`: the five-list presentation of the sign-split sheet for
  a set `S` of marked positives (splitting `τ` and the equivalence `F`);
* `sheetMarks_quad_free`, `sheetMarks_quad_marked`, `pow22_le`.
-/

@[expose] public section

namespace CatalanMeasure.Signed

open Set Finset
open scoped BigOperators
open CatalanMeasure.Parametric

noncomputable section

set_option maxRecDepth 100000
/-! ### The route II ratio is invariant under a permutation of the positives -/

theorem logRatioZ_comp_pos {k q q' : ℕ} (sp : ℕ) (xn : Fin k → ℝ) (gp : Fin q → ℝ)
    (e : Fin q' ≃ Fin q) :
    logRatioZ sp xn (fun p => gp (e p)) = logRatioZ sp xn gp := by
  unfold logRatioZ logPref
  have h1 : (∑ b, ∑ p, Real.log (1 - gp (e p) * xn b)) = ∑ b, ∑ p, Real.log (1 - gp p * xn b) :=
    Finset.sum_congr rfl fun b _ => Equiv.sum_comp e (fun p => Real.log (1 - gp p * xn b))
  have h2 : ∀ u : ℝ, ∏ p, (1 + 2 * gp (e p) * u + gp (e p) ^ 2) =
      ∏ p, (1 + 2 * gp p * u + gp p ^ 2) := fun u =>
    Equiv.prod_comp e (fun p => 1 + 2 * gp p * u + gp p ^ 2)
  simp only [h1, h2]

/-! ### Finset sums along an equivalence -/

section Transport

variable {ι A B : Type*} [Fintype ι] [Fintype A] [Fintype B] [DecidableEq ι]

theorem sum_Tc_eq (F : A ⊕ B ≃ ι) (T : Finset ι) (hA : ∀ a, F (Sum.inl a) ∉ T)
    (hB : ∀ b, F (Sum.inr b) ∈ T) (g : ι → ℝ) :
    ∑ a ∈ Tᶜ, g a = ∑ a : A, g (F (Sum.inl a)) := by
  have h : ∑ a ∈ Tᶜ, g a = ∑ a : ι, if a ∈ Tᶜ then g a else 0 := by
    rw [Finset.sum_ite_mem]; simp
  rw [h, ← Equiv.sum_comp F, Fintype.sum_sum_type]
  simp [hA, hB]

theorem sum_T_eq (F : A ⊕ B ≃ ι) (T : Finset ι) (hA : ∀ a, F (Sum.inl a) ∉ T)
    (hB : ∀ b, F (Sum.inr b) ∈ T) (g : ι → ℝ) :
    ∑ a ∈ T, g a = ∑ b : B, g (F (Sum.inr b)) := by
  have h : ∑ a ∈ T, g a = ∑ a : ι, if a ∈ T then g a else 0 := by
    rw [Finset.sum_ite_mem]; simp
  rw [h, ← Equiv.sum_comp F, Fintype.sum_sum_type]
  simp [hA, hB]

theorem dsum_Tc (F : A ⊕ B ≃ ι) (T : Finset ι) (hA : ∀ a, F (Sum.inl a) ∉ T)
    (hB : ∀ b, F (Sum.inr b) ∈ T) (f : ι → ι → ℝ) :
    ∑ a ∈ Tᶜ, ∑ b ∈ Tᶜ, f a b = ∑ a : A, ∑ a' : A, f (F (Sum.inl a)) (F (Sum.inl a')) := by
  rw [sum_Tc_eq F T hA hB (fun a => ∑ b ∈ Tᶜ, f a b)]
  exact Finset.sum_congr rfl fun a _ => sum_Tc_eq F T hA hB (f (F (Sum.inl a)))

theorem dsum_T (F : A ⊕ B ≃ ι) (T : Finset ι) (hA : ∀ a, F (Sum.inl a) ∉ T)
    (hB : ∀ b, F (Sum.inr b) ∈ T) (f : ι → ι → ℝ) :
    ∑ a ∈ T, ∑ b ∈ T, f a b = ∑ b : B, ∑ b' : B, f (F (Sum.inr b)) (F (Sum.inr b')) := by
  rw [sum_T_eq F T hA hB (fun a => ∑ b ∈ T, f a b)]
  exact Finset.sum_congr rfl fun a _ => sum_T_eq F T hA hB (f (F (Sum.inr a)))

theorem dsum_cross (F : A ⊕ B ≃ ι) (T : Finset ι) (hA : ∀ a, F (Sum.inl a) ∉ T)
    (hB : ∀ b, F (Sum.inr b) ∈ T) (f : ι → ι → ℝ) :
    ∑ a ∈ T, ∑ b ∈ Tᶜ, f a b = ∑ b : B, ∑ a : A, f (F (Sum.inr b)) (F (Sum.inl a)) := by
  rw [sum_T_eq F T hA hB (fun a => ∑ b ∈ Tᶜ, f a b)]
  exact Finset.sum_congr rfl fun a _ => sum_Tc_eq F T hA hB (f (F (Sum.inr a)))

/-- **`lamS` as the three energy sums of the lists**: the non-near rows `wa` (index `A`) and the
near rows `wb` (index `B`) of an equivalence `F : A ⊕ B ≃ ι` carrying `Tᶜ` and `T`. -/
theorem lamS_transport [DecidableEq A] [DecidableEq B] (F : A ⊕ B ≃ ι) (T : Finset ι)
    (hA : ∀ a, F (Sum.inl a) ∉ T) (hB : ∀ b, F (Sum.inr b) ∈ T) (u : ι → ℝ) (wa : A → ℝ)
    (wb : B → ℝ) (hua : ∀ a, u (F (Sum.inl a)) = wa a) (hub : ∀ b, u (F (Sum.inr b)) = wb b)
    (e : ℕ) :
    lamS u e T = (1 / 2) * (∑ a, ∑ a', lgd wa a a') + (1 / 2) * (∑ b, ∑ b', lgd wb b b') +
      (∑ b, ∑ a, Real.log (1 - wb b * wa a)) + (e : ℝ) * ∑ b, Real.log |wb b| := by
  unfold lamS
  rw [dsum_Tc F T hA hB (lgd u), dsum_T F T hA hB (lgd u), dsum_cross F T hA hB (lgc u),
    sum_T_eq F T hA hB (fun a => Real.log |u a|)]
  have h1 : ∀ a a', lgd u (F (Sum.inl a)) (F (Sum.inl a')) = lgd wa a a' := by
    intro a a'; unfold lgd; simp [F.injective.eq_iff, hua]
  have h2 : ∀ b b', lgd u (F (Sum.inr b)) (F (Sum.inr b')) = lgd wb b b' := by
    intro b b'; unfold lgd; simp [F.injective.eq_iff, hub]
  have h3 : ∀ b a, lgc u (F (Sum.inr b)) (F (Sum.inl a)) = Real.log (1 - wb b * wa a) := by
    intro b a; unfold lgc; rw [hua, hub]
  simp only [h1, h2, h3, hub]

end Transport

/-! ### Splitting a finite set by a subset; the combinatorial factor -/

/-- Split `Fin M` into the complement of `S₂` and `S₂` (the first-kind marked positives and the
near ones): `τ : Fin r ⊕ Fin s ≃ Fin M` with `inl ↦ S₂ᶜ`, `inr ↦ S₂`. -/
theorem exists_split_finset {M : ℕ} (S₂ : Finset (Fin M)) :
    ∃ (r s : ℕ) (τ : Fin r ⊕ Fin s ≃ Fin M), (∀ j, τ (Sum.inl j) ∉ S₂) ∧
      ∀ j, τ (Sum.inr j) ∈ S₂ := by
  classical
  let eS : {i // i ∈ S₂} ≃ Fin (Fintype.card {i // i ∈ S₂}) := Fintype.equivFin _
  let eT : {i // i ∉ S₂} ≃ Fin (Fintype.card {i // i ∉ S₂}) := Fintype.equivFin _
  refine ⟨Fintype.card {i // i ∉ S₂}, Fintype.card {i // i ∈ S₂},
    (Equiv.sumCongr eT.symm eS.symm).trans ((Equiv.sumComm _ _).trans
      (Equiv.sumCompl (fun i => i ∈ S₂))), ?_, ?_⟩
  · intro j
    simpa using (eT.symm j).2
  · intro j
    simpa using (eS.symm j).2

/-- **The five-list presentation of the sign-split sheet** (nodes `u` given by the appended lists
`xn ++ yn` and `gp ++ yp'`): for a set `S` of marked positives there are a splitting
`τ : Fin r ⊕ Fin s' ≃ Fin M` of the marked positives and an equivalence `F` of the five-list index
`Fin ((k+m1) + (q+r)) ⊕ Fin s'` onto the sign-split index, carrying the non-near rows (free, then
first-kind fixed) onto the complement of `S` and the near rows `yp' ∘ τ ∘ inr` onto `S`. -/
theorem near_split_data {k m1 q M : ℕ} (xn : Fin k → ℝ) (yn : Fin m1 → ℝ) (gp : Fin q → ℝ)
    (yp' : Fin M → ℝ) (u : Fin (k + m1) ⊕ Fin (q + M) → ℝ)
    (hu1 : ∀ b, u (Sum.inl b) = Fin.append xn yn b)
    (hu2 : ∀ p, u (Sum.inr p) = Fin.append gp yp' p)
    (S : Finset (Fin (q + M))) (hS : ∀ p ∈ S, ∃ j : Fin M, p = Fin.natAdd q j) :
    ∃ (r s' : ℕ) (τ : Fin r ⊕ Fin s' ≃ Fin M)
      (F : Fin ((k + m1) + (q + r)) ⊕ Fin s' ≃ Fin (k + m1) ⊕ Fin (q + M)),
      (∀ a, F (Sum.inl a) ∉ S.map Function.Embedding.inr) ∧
      (∀ b, F (Sum.inr b) ∈ S.map Function.Embedding.inr) ∧
      (∀ a, u (F (Sum.inl a)) =
        Fin.append (Fin.append xn yn) (Fin.append gp (fun j => yp' (τ (Sum.inl j)))) a) ∧
      (∀ b, u (F (Sum.inr b)) = yp' (τ (Sum.inr b))) := by
  classical
  obtain ⟨r, s', τ, h1, h2⟩ := exists_split_finset
    (Finset.univ.filter (fun j : Fin M => Fin.natAdd q j ∈ S))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  let Pe : Fin (q + r) ⊕ Fin s' ≃ Fin (q + M) :=
    ((finSumFinEquiv.symm.sumCongr (Equiv.refl (Fin s'))).trans
      ((Equiv.sumAssoc (Fin q) (Fin r) (Fin s')).trans
        ((Equiv.refl (Fin q)).sumCongr τ))).trans finSumFinEquiv
  let F : Fin ((k + m1) + (q + r)) ⊕ Fin s' ≃ Fin (k + m1) ⊕ Fin (q + M) :=
    ((finSumFinEquiv.symm.sumCongr (Equiv.refl (Fin s'))).trans
      ((Equiv.sumAssoc (Fin (k + m1)) (Fin (q + r)) (Fin s')).trans
        ((Equiv.refl (Fin (k + m1))).sumCongr Pe)))
  have hF1 : ∀ c : Fin (k + m1), F (Sum.inl (Fin.castAdd (q + r) c)) = Sum.inl c := by
    intro c; simp [F]
  have hF2 : ∀ p : Fin (q + r), F (Sum.inl (Fin.natAdd (k + m1) p)) = Sum.inr (Pe (Sum.inl p)) := by
    intro p; simp [F]
  have hF3 : ∀ j : Fin s', F (Sum.inr j) = Sum.inr (Pe (Sum.inr j)) := by
    intro j; simp [F]
  have hPe_r : ∀ j : Fin s', Pe (Sum.inr j) = Fin.natAdd q (τ (Sum.inr j)) := by
    intro j; simp [Pe]
  have hPe_c : ∀ b : Fin q, Pe (Sum.inl (Fin.castAdd r b)) = Fin.castAdd M b := by
    intro b; simp [Pe]
  have hPe_n : ∀ j : Fin r, Pe (Sum.inl (Fin.natAdd q j)) = Fin.natAdd q (τ (Sum.inl j)) := by
    intro j; simp [Pe]
  refine ⟨r, s', τ, F, ?_, ?_, ?_, ?_⟩
  · intro a
    obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective a
    rcases v with c | p
    · rw [finSumFinEquiv_apply_left, hF1]; simp
    · rw [finSumFinEquiv_apply_right, hF2]
      obtain ⟨w, rfl⟩ := finSumFinEquiv.surjective p
      rcases w with b | j
      · rw [finSumFinEquiv_apply_left, hPe_c]
        simp only [Finset.mem_map, Function.Embedding.inr_apply, Sum.inr.injEq, not_exists,
          not_and]
        intro p' hp' hpp
        obtain ⟨j', rfl⟩ := hS p' hp'
        exact absurd hpp (by
          simp only [Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
          have := b.isLt; omega)
      · rw [finSumFinEquiv_apply_right, hPe_n]
        simp only [Finset.mem_map, Function.Embedding.inr_apply, Sum.inr.injEq, not_exists,
          not_and]
        intro p' hp' hpp
        exact h1 j (hpp ▸ hp')
  · intro b
    rw [hF3, hPe_r]
    simp only [Finset.mem_map, Function.Embedding.inr_apply, Sum.inr.injEq]
    exact ⟨_, h2 b, rfl⟩
  · intro a
    obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective a
    rcases v with c | p
    · rw [finSumFinEquiv_apply_left, hF1, hu1]
      simp
    · rw [finSumFinEquiv_apply_right, hF2, hu2]
      obtain ⟨w, rfl⟩ := finSumFinEquiv.surjective p
      rcases w with b | j
      · rw [finSumFinEquiv_apply_left, hPe_c]
        simp
      · rw [finSumFinEquiv_apply_right, hPe_n]
        simp
  · intro b
    rw [hF3, hu2, hPe_r]
    simp

/-! ### The marks of the quad index -/

theorem sheetMarks_quad_free {P : Parameters} {N k q m1 m2 p m : ℕ} (hpm : p + m = P.n N)
    (σx : Fin k ⊕ Fin q ≃ Fin p) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m) (b : Fin q) :
    sheetMarks hpm (((quadEquiv σx σy).trans (finCongr hpm))
      (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inl b))))) = false := by
  simp [sheetMarks, quadEquiv]

theorem sheetMarks_quad_marked {P : Parameters} {N k q m1 m2 p m : ℕ} (hpm : p + m = P.n N)
    (σx : Fin k ⊕ Fin q ≃ Fin p) (σy : Fin m1 ⊕ Fin m2 ≃ Fin m) (j : Fin m2) :
    sheetMarks hpm (((quadEquiv σx σy).trans (finCongr hpm))
      (finSumFinEquiv (Sum.inr (finSumFinEquiv (Sum.inr j))))) = true := by
  simp [sheetMarks, quadEquiv]

/-! ### The class branch of the marked sheet with near-type rows -/

end
end CatalanMeasure.Signed
