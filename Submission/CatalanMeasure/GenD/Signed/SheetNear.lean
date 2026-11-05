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

section ClassNear

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan Filter
  CatalanMeasure.GenD.Signed

/-- **The left side of `signed_second_energy_near_nodes` for five lists** with the exact fields of
the 532 identity `log_groupedProduct`: the free-row field, the first-kind marked field
`groupedMarkedField`, the near field `groupedNearField`, the factor-free column field, and the
grouped constant at the actual counts. -/
def nearLHS (P : Parameters) (N : ℕ) {k q m1 m2 s : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ)
    (yn : Fin m1 → ℝ) (yp : Fin m2 → ℝ) (zp : Fin s → ℝ) (col : Fin (k + q) → ℝ) : ℝ :=
  groupedConstant P N (k + q) (m1 + m2) s +
    pinOffDiagonalInteraction (P.n N : ℝ) 1 (Fin.append xn gp) col +
    (∑ i, ∑ j ∈ Finset.Ioi i,
      Real.log |Fin.append (Fin.append xn yn) (Fin.append gp yp) j -
        Fin.append (Fin.append xn yn) (Fin.append gp yp) i|) / (P.n N : ℝ) ^ 2 +
    (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |zp j - zp i|) / (P.n N : ℝ) ^ 2 +
    (∑ i, ∑ j, Real.log (1 -
      Fin.append (Fin.append xn yn) (Fin.append gp yp) i * zp j)) / (P.n N : ℝ) ^ 2 +
    ((∑ b, populationPhysicalFreeField P N (xn b)) + ∑ p, populationPhysicalFreeField P N (gp p)) /
      (P.n N : ℝ) +
    ((∑ j, groupedMarkedField P N (yn j)) + ∑ j, groupedMarkedField P N (yp j)) / (P.n N : ℝ) +
    (∑ j, groupedNearField P N (zp j)) / (P.n N : ℝ) +
    (∑ j, populationPhysicalColumnField P N (0 + 0) (col j)) / (P.n N : ℝ) +
    logRatioZ (q + (m2 + s) - P.g N) (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) /
      (P.n N : ℝ) ^ 2

end ClassNear

section SNear

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan Filter
  CatalanMeasure.GenD.Signed

theorem groupedConstant_split (P : Parameters) (N r0 a b : ℕ) :
    groupedConstant P N r0 a b = groupedConstant P N r0 0 0 +
      ((a + b : ℕ) : ℝ) * ((P.n N - P.g N - 1 : ℕ) : ℝ) / (P.n N : ℝ) ^ 2 * Real.log 2 := by
  unfold groupedConstant
  push_cast
  ring

theorem log_msw_eq {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) (y : ℝ) :
    Real.log (markedSheetWeight P N y) = (P.n N : ℝ) * groupedMarkedField P N y +
      ((P.n N - P.g N - 1 : ℕ) : ℝ) * Real.log 2 := by
  have hn : (P.n N : ℝ) ≠ 0 := by exact_mod_cast (n_pos hP hN).ne'
  rw [log_markedSheetWeight]
  unfold groupedMarkedField
  field_simp
  ring

theorem near_field_eq {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N) (y : ℝ) :
    (P.n N : ℝ) * groupedNearField P N y = (P.n N : ℝ) * groupedMarkedField P N y +
      ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ) * Real.log |y| := by
  have hn : (P.n N : ℝ) ≠ 0 := by exact_mod_cast (n_pos hP hN).ne'
  unfold groupedNearField
  field_simp

end SNear

section SNear2

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan Filter
  CatalanMeasure.GenD.Signed

set_option maxHeartbeats 1600000 in
/-- **The `S`-term of the sheet bound.**  For a set `S` of marked positives of the sign-split
sheet (nodes `u`, presented by the lists `xn ++ yn`, `gp ++ yp'`), the near-type term
`Zx · exp LR · pin · M · exp (lamS)` is at most `exp (n² Bd)`, from the energy inequality `hE`
for the five lists of every splitting of the marked positives, the free-row identity `hfree`
(from `log_groupedProduct_free`) and the exact marked-row weights. -/
theorem near_Sterm_le {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    {k q m1 M : ℕ} (xn : Fin k → ℝ) (gp : Fin q → ℝ) (yn : Fin m1 → ℝ) (yp' : Fin M → ℝ)
    (col : Fin (k + q) → ℝ) (u : Fin (k + m1) ⊕ Fin (q + M) → ℝ)
    (hu : Function.Injective u)
    (hu1 : ∀ b, u (Sum.inl b) = Fin.append xn yn b)
    (hu2 : ∀ p, u (Sum.inr p) = Fin.append gp yp' p)
    (Zx pin Mp : ℝ) (hZx : 0 < Zx) (hpin : 0 < pin) (hMp : 0 < Mp)
    (hfree : Real.log Zx + Real.log pin =
      (P.n N : ℝ) ^ 2 * (groupedConstant P N (k + q) 0 0 +
        pinOffDiagonalInteraction (P.n N : ℝ) 1 (Fin.append xn gp) col) +
      (P.n N : ℝ) * (((∑ b, populationPhysicalFreeField P N (xn b)) +
        ∑ p, populationPhysicalFreeField P N (gp p)) +
        ∑ j, populationPhysicalColumnField P N (0 + 0) (col j)))
    (hMp' : Real.log Mp = ∑ j, Real.log (markedSheetWeight P N (yn j)) +
      ∑ j, Real.log (markedSheetWeight P N (yp' j)))
    (hinjF : Function.Injective (Fin.append xn gp))
    (S : Finset (Fin (q + M))) (hS : ∀ p ∈ S, ∃ j : Fin M, p = Fin.natAdd q j)
    (Bd : ℝ)
    (hE : ∀ (r s' : ℕ) (τ : Fin r ⊕ Fin s' ≃ Fin M),
      Function.Injective (Fin.append (Fin.append xn yn)
        (Fin.append gp (fun j => yp' (τ (Sum.inl j))))) →
      nearLHS P N xn gp yn (fun j => yp' (τ (Sum.inl j))) (fun j => yp' (τ (Sum.inr j))) col ≤ Bd) :
    Zx * Real.exp (logRatioZ (q + M - P.g N) (Fin.append xn yn) (Fin.append gp yp')) * pin * Mp *
      Real.exp (lamS u (P.n N - 1 - 2 * P.g N) (S.map Function.Embedding.inr)) ≤
      Real.exp ((P.n N : ℝ) ^ 2 * Bd) := by
  classical
  obtain ⟨r, s', τ, F, hF1, hF2, hF3, hF4⟩ := near_split_data xn yn gp yp' u hu1 hu2 S hS
  have hM : M = r + s' := by simpa using (Fintype.card_congr τ).symm
  have hn : (P.n N : ℝ) ≠ 0 := by exact_mod_cast (n_pos hP hN).ne'
  have hnpos : (0 : ℝ) < (P.n N : ℝ) := by exact_mod_cast n_pos hP hN
  have hn2 : (0 : ℝ) < (P.n N : ℝ) ^ 2 := by positivity
  -- the lists
  obtain ⟨yp, hyp⟩ : ∃ yp : Fin r → ℝ, yp = fun j => yp' (τ (Sum.inl j)) := ⟨_, rfl⟩
  obtain ⟨zp, hzp⟩ : ∃ zp : Fin s' → ℝ, zp = fun j => yp' (τ (Sum.inr j)) := ⟨_, rfl⟩
  obtain ⟨wa, hwa⟩ : ∃ wa : Fin ((k + m1) + (q + r)) → ℝ,
      wa = Fin.append (Fin.append xn yn) (Fin.append gp yp) := ⟨_, rfl⟩
  have hF3' : ∀ a, u (F (Sum.inl a)) = wa a := fun a => by rw [hF3, hwa, hyp]
  have hF4' : ∀ b, u (F (Sum.inr b)) = zp b := fun b => by rw [hF4, hzp]
  have hwainj : Function.Injective wa := by
    intro a b hab
    have : u (F (Sum.inl a)) = u (F (Sum.inl b)) := by rw [hF3', hF3', hab]
    exact Sum.inl_injective (F.injective (hu this))
  have hlam := lamS_transport F (S.map Function.Embedding.inr) hF1 hF2 u wa zp hF3' hF4'
    (P.n N - 1 - 2 * P.g N)
  -- pair sums
  have hVa : (1 / 2) * (∑ a, ∑ a', lgd wa a a') =
      ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |wa j - wa i| := by
    have h := sum_offdiag_eq_two_mul (fun i j => Real.log |wa i - wa j|)
      (fun i j => by rw [abs_sub_comm])
    have h' : (∑ a, ∑ a', lgd wa a a') =
        ∑ i, ∑ j, if i = j then (0 : ℝ) else Real.log |wa i - wa j| := rfl
    rw [h', h]
    have : ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |wa j - wa i| =
        ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |wa i - wa j| :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [abs_sub_comm]
    rw [this]; ring
  have hVb : (1 / 2) * (∑ b, ∑ b', lgd zp b b') =
      ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |zp j - zp i| := by
    have h := sum_offdiag_eq_two_mul (fun i j => Real.log |zp i - zp j|)
      (fun i j => by rw [abs_sub_comm])
    have h' : (∑ b, ∑ b', lgd zp b b') =
        ∑ i, ∑ j, if i = j then (0 : ℝ) else Real.log |zp i - zp j| := rfl
    rw [h', h]
    have : ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |zp j - zp i| =
        ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |zp i - zp j| :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [abs_sub_comm]
    rw [this]; ring
  have hCr : (∑ b, ∑ a, Real.log (1 - zp b * wa a)) =
      ∑ i, ∑ j, Real.log (1 - wa i * zp j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [mul_comm]
  rw [hVa, hVb, hCr] at hlam
  -- the route II ratio
  let ρ : Fin (q + (r + s')) ≃ Fin (q + M) :=
    finSumFinEquiv.symm.trans (((Equiv.refl (Fin q)).sumCongr
      (finSumFinEquiv.symm.trans τ)).trans finSumFinEquiv)
  have hρ : (fun i => Fin.append gp yp' (ρ i)) = Fin.append gp (Fin.append yp zp) := by
    funext i
    obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective i
    rcases v with b | j
    · simp [ρ]
    · obtain ⟨c, rfl⟩ := finSumFinEquiv.surjective j
      rcases c with c | c <;> simp [ρ, hyp, hzp]
  have hsp : q + M - P.g N = q + (r + s') - P.g N := by rw [hM]
  have hLR : logRatioZ (q + M - P.g N) (Fin.append xn yn) (Fin.append gp yp') =
      logRatioZ (q + (r + s') - P.g N) (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) := by
    rw [← hρ, logRatioZ_comp_pos, hsp]
  -- the energy inequality
  have hinjNN : Function.Injective (Fin.append (Fin.append xn yn)
      (Fin.append gp (fun j => yp' (τ (Sum.inl j))))) := by
    have := hwainj; rw [hwa, hyp] at this; exact this
  have hEapp : nearLHS P N xn gp yn yp zp col ≤ Bd := by
    have := hE r s' τ hinjNN
    rw [hyp, hzp]; exact this
  -- the log of the term
  have hpos : 0 < Zx * Real.exp (logRatioZ (q + M - P.g N) (Fin.append xn yn)
      (Fin.append gp yp')) * pin * Mp *
      Real.exp (lamS u (P.n N - 1 - 2 * P.g N) (S.map Function.Embedding.inr)) :=
    mul_pos (mul_pos (mul_pos (mul_pos hZx (Real.exp_pos _)) hpin) hMp) (Real.exp_pos _)
  refine (Real.log_le_iff_le_exp hpos).mp ?_
  rw [Real.log_mul (mul_pos (mul_pos (mul_pos hZx (Real.exp_pos _)) hpin) hMp).ne'
      (Real.exp_pos _).ne',
    Real.log_mul (mul_pos (mul_pos hZx (Real.exp_pos _)) hpin).ne' hMp.ne',
    Real.log_mul (mul_pos hZx (Real.exp_pos _)).ne' hpin.ne',
    Real.log_mul hZx.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp, hlam, hLR]
  -- sums over the marked rows
  have hMsum : (∑ j, Real.log (markedSheetWeight P N (yp' j))) =
      (∑ j, Real.log (markedSheetWeight P N (yp j))) +
        ∑ j, Real.log (markedSheetWeight P N (zp j)) := by
    rw [← Equiv.sum_comp τ, Fintype.sum_sum_type]
    simp [hyp, hzp]
  have hcnt : ((m1 + r + s' : ℕ) : ℝ) = (m1 : ℝ) + r + s' := by push_cast; ring
  have hMw : ∀ {c : ℕ} (v : Fin c → ℝ), (∑ j, Real.log (markedSheetWeight P N (v j))) =
      (P.n N : ℝ) * (∑ j, groupedMarkedField P N (v j)) +
        (c : ℝ) * (((P.n N - P.g N - 1 : ℕ) : ℝ) * Real.log 2) := by
    intro c v
    simp only [log_msw_eq hP hN, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hNe : ∀ (v : Fin s' → ℝ),
      (∑ j, groupedNearField P N (v j)) * (P.n N : ℝ) =
        (∑ j, groupedMarkedField P N (v j)) * (P.n N : ℝ) +
          ((P.n N - 1 - 2 * P.g N : ℕ) : ℝ) * ∑ j, Real.log |v j| := by
    intro v
    rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := near_field_eq hP hN (v j)
    linarith
  have hkey : (P.n N : ℝ) ^ 2 * nearLHS P N xn gp yn yp zp col =
      (P.n N : ℝ) ^ 2 * (groupedConstant P N (k + q) 0 0 +
        pinOffDiagonalInteraction (P.n N : ℝ) 1 (Fin.append xn gp) col) +
      ((m1 : ℝ) + r + s') * ((P.n N - P.g N - 1 : ℕ) : ℝ) * Real.log 2 +
      (∑ i, ∑ j ∈ Finset.Ioi i,
        Real.log |wa j - wa i|) + (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |zp j - zp i|) +
      (∑ i, ∑ j, Real.log (1 - wa i * zp j)) +
      (P.n N : ℝ) * (((∑ b, populationPhysicalFreeField P N (xn b)) +
        ∑ p, populationPhysicalFreeField P N (gp p)) +
        ((∑ j, groupedMarkedField P N (yn j)) + ∑ j, groupedMarkedField P N (yp j)) +
        (∑ j, groupedNearField P N (zp j)) +
        ∑ j, populationPhysicalColumnField P N (0 + 0) (col j)) +
      logRatioZ (q + (r + s') - P.g N) (Fin.append xn yn) (Fin.append gp (Fin.append yp zp)) := by
    unfold nearLHS
    rw [groupedConstant_split, ← hwa, hcnt]
    field_simp
    ring
  have hNeq := hNe zp
  have hMyn := hMw yn
  have hMyp := hMw yp
  have hMzp := hMw zp
  have hbound := mul_le_mul_of_nonneg_left hEapp hn2.le
  rw [hMp', hMsum]
  nlinarith [hfree, hMyn, hMyp, hMzp, hNeq, hkey, hbound]

end SNear2

section SNear3

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan Filter
  CatalanMeasure.GenD.Signed

/-- **Class-branch bound for the marked sheet with near-type rows (deterministic).**  Lemma T for
ALL positive nodes (`hT`), the energy inequality `hE` for the five lists of every splitting of
the marked positives (the near rows being the set `S` of Lemma 17.43.1), and the exact marked-row
weights give `markedSheetCore ≤ 22^(q + m2') exp (n² Bd)`. -/
theorem near_class_core_le {P : Parameters} (hP : Admissible P) {N : ℕ} (hN : 0 < N)
    {m k q m1 m2' : ℕ} (hpm : k + q + m = P.n N)
    (σx : Fin k ⊕ Fin q ≃ Fin (k + q)) (σy : Fin m1 ⊕ Fin m2' ≃ Fin m)
    (x col : Fin (k + q) → ℝ) (y : Fin m → ℝ)
    (hx : ∀ i, x i ∈ Ioo (-1 : ℝ) 1) (hx0 : ∀ i, x i ≠ 0)
    (hy : ∀ j, y j ∈ Ioo (-1 : ℝ) 1) (hy0 : ∀ j, y j ≠ 0)
    (hs : ∀ i, col i ∈ Ioo (0 : ℝ) 1) (hzi : Function.Injective (Fin.append x y))
    (hsi : Function.Injective col)
    (hxneg : ∀ b, x (σx (Sum.inl b)) < 0) (hxpos : ∀ b, 0 < x (σx (Sum.inr b)))
    (hyneg : ∀ b, y (σy (Sum.inl b)) < 0) (hypos : ∀ b, 0 < y (σy (Sum.inr b)))
    (hk : 0 < k) (hq : 2 * P.g N < q)
    (hT : ∀ c : Fin (P.n N) → ℝ,
      |∑ a ∈ Finset.univ.filter (fun a => 0 < sheetNodes hpm x y a),
        bDeriv (sheetNodes hpm x y) a * sheetNodes hpm x y a ^ (P.n N - 1 - 2 * P.g N) *
          c a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, c a * c b /
          (1 - sheetNodes hpm x y a * sheetNodes hpm x y b))
    (Bd : ℝ)
    (hE : ∀ (r s' : ℕ) (τ : Fin r ⊕ Fin s' ≃ Fin m2'),
      Function.Injective (Fin.append (Fin.append (fun b => x (σx (Sum.inl b)))
          (fun b => y (σy (Sum.inl b))))
        (Fin.append (fun b => x (σx (Sum.inr b))) (fun j => y (σy (Sum.inr (τ (Sum.inl j))))))) →
      nearLHS P N (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))
        (fun b => y (σy (Sum.inl b))) (fun j => y (σy (Sum.inr (τ (Sum.inl j)))))
        (fun j => y (σy (Sum.inr (τ (Sum.inr j))))) col ≤ Bd) :
    markedSheetCore P N hpm x y col ≤ 22 ^ (q + m2') * Real.exp ((P.n N : ℝ) ^ 2 * Bd) := by
  classical
  have hn1 : 1 ≤ P.n N := n_pos hP hN
  have hg2 := two_g_lt_n hP hN
  have hnR : (0 : ℝ) < (P.n N : ℝ) := by exact_mod_cast hn1
  have hn2 : (0 : ℝ) < (P.n N : ℝ) ^ 2 := by positivity
  obtain ⟨z, hzd⟩ : ∃ z : Fin (P.n N) → ℝ, z = sheetNodes hpm x y := ⟨_, rfl⟩
  obtain ⟨mk, hmkd⟩ : ∃ mk : Fin (P.n N) → Bool, mk = sheetMarks hpm := ⟨_, rfl⟩
  rw [← hzd] at hT
  obtain ⟨e4, he4⟩ : ∃ e4 : Fin ((k + m1) + (q + m2')) ≃ Fin (P.n N),
      e4 = (quadEquiv σx σy).trans (finCongr hpm) := ⟨_, rfl⟩
  have hzZ : ∀ i, z (e4 i) = quadNodes σx σy x y i := by
    intro i
    rw [hzd, he4, quadNodes_apply]
    simp [sheetNodes]
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin (k + m1) ⊕ Fin (q + m2') ≃ Fin (P.n N),
      σ = finSumFinEquiv.trans e4 := ⟨_, rfl⟩
  have hzσl : ∀ b, z (σ (Sum.inl b)) =
      Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))) b := by
    intro b
    rw [hσ]
    simp only [Equiv.trans_apply, finSumFinEquiv_apply_left]
    rw [hzZ]
    unfold quadNodes
    simp
  have hzσr : ∀ b, z (σ (Sum.inr b)) =
      Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b))) b := by
    intro b
    rw [hσ]
    simp only [Equiv.trans_apply, finSumFinEquiv_apply_right]
    rw [hzZ]
    unfold quadNodes
    simp
  have hzm : ∀ i, z i ∈ Ioo (-1 : ℝ) 1 := fun i => by
    rw [hzd]; exact append_forall (Q := fun t => t ∈ Ioo (-1 : ℝ) 1) hx hy _
  have hz1 : ∀ i, |z i| < 1 := fun i => abs_lt.mpr (hzm i)
  have hz0 : ∀ i, z i ≠ 0 := fun i => by
    rw [hzd]; exact append_forall (Q := fun t => t ≠ 0) hx0 hy0 _
  have hzinj : Function.Injective z := by
    rw [hzd]; exact hzi.comp (Fin.cast_injective _)
  have hxi : Function.Injective x := by
    intro a b hab
    have := hzi (show Fin.append x y (Fin.castAdd m a) = Fin.append x y (Fin.castAdd m b) by
      simpa using hab)
    simpa using this
  have hneg : ∀ b, z (σ (Sum.inl b)) < 0 := fun b => by
    rw [hzσl]; exact append_forall (Q := fun t => t < 0) hxneg hyneg b
  have hpos : ∀ b, 0 < z (σ (Sum.inr b)) := fun b => by
    rw [hzσr]; exact append_forall (Q := fun t => 0 < t) hxpos hypos b
  have hdet := abs_det_laurent_le_marked_expand (g := P.g N) σ z mk hzinj hz1 hz0 hneg hpos
    (by omega) (by omega) hT
  -- marks of the positives
  have hmkfree : ∀ b : Fin q, mk (σ (Sum.inr (Fin.castAdd m2' b))) = false := by
    intro b
    have := sheetMarks_quad_free hpm σx σy b
    simp only [finSumFinEquiv_apply_left] at this
    rw [hmkd, hσ]
    simpa [he4] using this
  -- the sheet core in terms of the Laurent determinant
  have hcore : markedSheetCore P N hpm x y col =
      |(markedLaurentMatrix (P.g N) z mk).det| * (∏ j, paramRowNodeWeight P N (y j)) *
        paramPinPrincipal P N x col /
          ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| := by
    rw [hzd, hmkd]; rfl
  have hRpos : 0 < ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| := by
    apply Finset.prod_pos
    intro j _
    apply abs_pos.mpr
    apply rowCommonFactor_eval_ne_zero_of P N
    · unfold realCoordinateInv
      exact div_ne_zero (mul_ne_zero (by norm_num) (hy0 j)) (by positivity)
    · exact (sub_pos.mp (one_sub_realCoordinateInv_pos (hy j))).ne
  have hWnn : 0 ≤ ∏ j, paramRowNodeWeight P N (y j) :=
    Finset.prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j)
  have hpinpos := paramPinPrincipal_pos hP hN x col hx hs hx0 hxi hsi
  have hZ : ∏ i, |z i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) =
      (∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
        ∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) := by
    rw [hzd]
    unfold sheetNodes
    have := prod_fin_cast hpm (fun j : Fin (k + q + m) =>
      |Fin.append x y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)))
    rw [this, Fin.prod_univ_add]
    simp
  have hcancel : (∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ))) *
        (∏ j, paramRowNodeWeight P N (y j)) =
      (∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))|) *
        ∏ j, markedSheetWeight P N (y j) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ =>
      marked_sheet_weight_cancellation hP hN (hy j) (hy0 j)
  -- notation
  obtain ⟨Zx, hZx⟩ : ∃ Zx : ℝ, Zx = ∏ i, |x i| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) := ⟨_, rfl⟩
  obtain ⟨Zy, hZy⟩ : ∃ Zy : ℝ, Zy = ∏ j, |y j| ^ ((P.g N : ℤ) - (P.n N - 1 : ℕ)) := ⟨_, rfl⟩
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∏ j, paramRowNodeWeight P N (y j) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ,
      R = ∏ j, |(rowCommonFactor P N).eval (realCoordinateInv (y j))| := ⟨_, rfl⟩
  obtain ⟨Mp, hMp⟩ : ∃ Mp : ℝ, Mp = ∏ j, markedSheetWeight P N (y j) := ⟨_, rfl⟩
  obtain ⟨pin, hpin⟩ : ∃ pin : ℝ, pin = paramPinPrincipal P N x col := ⟨_, rfl⟩
  rw [← hZx, ← hZy] at hZ
  rw [← hZy, ← hW, ← hR, ← hMp] at hcancel
  rw [← hW, ← hpin, ← hR] at hcore
  rw [← hR] at hRpos
  rw [← hW] at hWnn
  rw [← hpin] at hpinpos
  have hZxpos : 0 < Zx := by
    rw [hZx]; exact Finset.prod_pos fun i _ => zpow_pos (abs_pos.mpr (hx0 i)) _
  have hMpos : 0 < Mp := by
    rw [hMp]; exact Finset.prod_pos fun j _ => markedSheetWeight_pos P N _
  -- the free-row identity
  have hGP := log_groupedProduct_free hP hN x col hx hs hx0 hxi hsi
  have hGPeq := groupedProduct_free_eq P N x col
  have hVx : Real.log |(Matrix.vandermonde x).det| =
      ∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i| := by
    rw [Matrix.det_vandermonde]; exact log_abs_vandermonde x hxi
  have hVxpos : 0 < |(Matrix.vandermonde x).det| :=
    abs_pos.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hxi)
  have hlogGP : Real.log (groupedProduct P N x e0 e0 col) =
      Real.log Zx + (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) + Real.log pin := by
    rw [hGPeq, ← hZx, ← hpin, Real.log_mul (mul_pos hZxpos hVxpos).ne' hpinpos.ne',
      Real.log_mul hZxpos.ne' hVxpos.ne', hVx]
  have hnne : (P.n N : ℝ) ≠ 0 := hnR.ne'
  have hfreeA : Real.log Zx + Real.log pin =
      (P.n N : ℝ) ^ 2 * (groupedConstant P N (k + q) 0 0 +
        pinOffDiagonalInteraction (P.n N : ℝ) 1 x col) +
      (P.n N : ℝ) * ((∑ i, populationPhysicalFreeField P N (x i)) +
        ∑ j, populationPhysicalColumnField P N (0 + 0) (col j)) := by
    have e : (P.n N : ℝ) ^ 2 * (groupedConstant P N (k + q) 0 0 +
        pinOffDiagonalInteraction (P.n N : ℝ) 1 x col +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) / (P.n N : ℝ) ^ 2 +
        (∑ i, populationPhysicalFreeField P N (x i)) / (P.n N : ℝ) +
        (∑ j, populationPhysicalColumnField P N (0 + 0) (col j)) / (P.n N : ℝ)) =
        (P.n N : ℝ) ^ 2 * (groupedConstant P N (k + q) 0 0 +
          pinOffDiagonalInteraction (P.n N : ℝ) 1 x col) +
        (∑ i, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i|) +
        (P.n N : ℝ) * ((∑ i, populationPhysicalFreeField P N (x i)) +
          ∑ j, populationPhysicalColumnField P N (0 + 0) (col j)) := by
      field_simp
      ring
    have h' := hGP
    rw [hlogGP, e] at h'
    linarith
  have hpinR : pinOffDiagonalInteraction (P.n N : ℝ) 1
      (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))) col =
      pinOffDiagonalInteraction (P.n N : ℝ) 1 x col := by
    rw [append_split_eq σx x]
    have := pinOff_perm (P.n N : ℝ) 1 x col (splitEquiv σx) (Equiv.refl _)
    simpa using this
  have hSRx : (∑ i, populationPhysicalFreeField P N (x i)) =
      (∑ b, populationPhysicalFreeField P N (x (σx (Sum.inl b)))) +
        ∑ b, populationPhysicalFreeField P N (x (σx (Sum.inr b))) := by
    rw [← Equiv.sum_comp σx (fun i => populationPhysicalFreeField P N (x i)),
      Fintype.sum_sum_type]
  have hfreeL : Real.log Zx + Real.log pin =
      (P.n N : ℝ) ^ 2 * (groupedConstant P N (k + q) 0 0 +
        pinOffDiagonalInteraction (P.n N : ℝ) 1
          (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))) col) +
      (P.n N : ℝ) * (((∑ b, populationPhysicalFreeField P N (x (σx (Sum.inl b)))) +
        ∑ p, populationPhysicalFreeField P N (x (σx (Sum.inr p)))) +
        ∑ j, populationPhysicalColumnField P N (0 + 0) (col j)) := by
    rw [hpinR, hfreeA, hSRx]
  have hMlogL : Real.log Mp = ∑ j, Real.log (markedSheetWeight P N (y (σy (Sum.inl j)))) +
      ∑ j, Real.log (markedSheetWeight P N (y (σy (Sum.inr j)))) := by
    rw [hMp, Real.log_prod (fun j _ => (markedSheetWeight_pos P N _).ne'),
      ← Equiv.sum_comp σy (fun j => Real.log (markedSheetWeight P N (y j))),
      Fintype.sum_sum_type]
  have hinjF : Function.Injective
      (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))) := by
    rw [append_split_eq]; exact hxi.comp (splitEquiv σx).injective
  -- the route II ratio of the sign split
  have hLRe : logRatioZ (q + m2' - P.g N) (fun b => z (σ (Sum.inl b)))
      (fun b => z (σ (Sum.inr b))) =
      logRatioZ (q + m2' - P.g N)
        (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))))
        (Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b)))) := by
    congr 1 <;> funext b
    · exact hzσl b
    · exact hzσr b
  rw [hLRe] at hdet
  -- one S-term
  have hS : ∀ S : Finset (Fin (q + m2')), (∀ p ∈ S, mk (σ (Sum.inr p)) = true) →
      Zx * Real.exp (logRatioZ (q + m2' - P.g N)
        (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))))
        (Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b))))) * pin * Mp *
        Real.exp (lamS (fun i => z (σ i)) (P.n N - 1 - 2 * P.g N)
          (S.map Function.Embedding.inr)) ≤ Real.exp ((P.n N : ℝ) ^ 2 * Bd) := by
    intro S hSm
    have hSm' : ∀ p ∈ S, ∃ j : Fin m2', p = Fin.natAdd q j := by
      intro p hp
      have h := hSm p hp
      obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective p
      rcases v with b | j
      · rw [finSumFinEquiv_apply_left, hmkfree] at h; simp at h
      · exact ⟨j, by simp⟩
    exact near_Sterm_le hP hN (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))
      (fun b => y (σy (Sum.inl b))) (fun b => y (σy (Sum.inr b))) col (fun i => z (σ i))
      (hzinj.comp σ.injective) hzσl hzσr Zx pin Mp hZxpos hpinpos hMpos hfreeL hMlogL hinjF S
      hSm' Bd (fun r s' τ hinj => hE r s' τ hinj)
  -- the sum over S
  obtain ⟨E, hEd⟩ : ∃ E : ℝ, E = Real.exp (logRatioZ (q + m2' - P.g N)
        (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => y (σy (Sum.inl b))))
        (Fin.append (fun b => x (σx (Sum.inr b))) (fun b => y (σy (Sum.inr b))))) := ⟨_, rfl⟩
  rw [← hEd] at hdet hS
  have hEpos : 0 < E := by rw [hEd]; exact Real.exp_pos _
  obtain ⟨t, ht⟩ : ∃ t : Finset (Fin (q + m2')) → ℝ, t = fun S =>
      (if ∀ p ∈ S, mk (σ (Sum.inr p)) = true then
        (6 : ℝ) ^ S.card * 11 ^ (q + m2' - S.card) *
          Real.exp (lamS (fun i => z (σ i)) (P.n N - 1 - 2 * P.g N)
            (S.map Function.Embedding.inr)) else 0) := ⟨_, rfl⟩
  have hdet' : |(markedLaurentMatrix (P.g N) z mk).det| ≤
      (Zx * Zy) * E * ∑ S, t S := by
    rw [ht, ← hZ]; exact hdet
  have hstep1 : markedSheetCore P N hpm x y col ≤ Zx * E * pin * Mp * ∑ S, t S := by
    rw [hcore, div_le_iff₀ hRpos]
    calc |(markedLaurentMatrix (P.g N) z mk).det| * W * pin
        ≤ ((Zx * Zy) * E * ∑ S, t S) * W * pin := by
          have h0 : 0 ≤ W := hWnn
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdet' h0) hpinpos.le
      _ = Zx * E * (∑ S, t S) * pin * (Zy * W) := by ring
      _ = Zx * E * (∑ S, t S) * pin * (R * Mp) := by rw [hcancel]
      _ = (Zx * E * pin * Mp * ∑ S, t S) * R := by ring
  have hQ : 0 ≤ Zx * E * pin * Mp := by positivity
  have hterm : ∀ S : Finset (Fin (q + m2')),
      Zx * E * pin * Mp * t S ≤ 11 ^ (q + m2') * Real.exp ((P.n N : ℝ) ^ 2 * Bd) := by
    intro S
    rw [ht]
    by_cases hc : ∀ p ∈ S, mk (σ (Sum.inr p)) = true
    · simp only [if_pos hc]
      have h6 : (6 : ℝ) ^ S.card * 11 ^ (q + m2' - S.card) ≤ 11 ^ (q + m2') := by
        have hle : S.card ≤ q + m2' := by
          have := Finset.card_le_univ S; simpa using this
        calc (6 : ℝ) ^ S.card * 11 ^ (q + m2' - S.card) ≤ 11 ^ S.card * 11 ^ (q + m2' - S.card) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) (by norm_num) _)
                (by positivity)
          _ = 11 ^ (q + m2') := by rw [← pow_add]; congr 1; omega
      have h1 := hS S hc
      calc Zx * E * pin * Mp * ((6 : ℝ) ^ S.card * 11 ^ (q + m2' - S.card) *
            Real.exp (lamS (fun i => z (σ i)) (P.n N - 1 - 2 * P.g N)
              (S.map Function.Embedding.inr)))
          = ((6 : ℝ) ^ S.card * 11 ^ (q + m2' - S.card)) *
            (Zx * E * pin * Mp * Real.exp (lamS (fun i => z (σ i)) (P.n N - 1 - 2 * P.g N)
              (S.map Function.Embedding.inr))) := by ring
        _ ≤ 11 ^ (q + m2') * Real.exp ((P.n N : ℝ) ^ 2 * Bd) :=
          mul_le_mul h6 h1 (by positivity) (by positivity)
    · simp only [if_neg hc, mul_zero]; positivity
  calc markedSheetCore P N hpm x y col ≤ Zx * E * pin * Mp * ∑ S, t S := hstep1
    _ = ∑ S, Zx * E * pin * Mp * t S := by rw [Finset.mul_sum]
    _ ≤ ∑ _S : Finset (Fin (q + m2')), 11 ^ (q + m2') * Real.exp ((P.n N : ℝ) ^ 2 * Bd) :=
        Finset.sum_le_sum fun S _ => hterm S
    _ = 22 ^ (q + m2') * Real.exp ((P.n N : ℝ) ^ 2 * Bd) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin,
          nsmul_eq_mul]
        push_cast
        rw [show (22 : ℝ) ^ (q + m2') = 2 ^ (q + m2') * 11 ^ (q + m2') by
          rw [← mul_pow]; norm_num]
        ring

end SNear3

/-- `22^q ≤ (1 + 10 e^12 n)^n` for `q ≤ n`, `1 ≤ n` (the subsets `S` times `11^q`). -/
theorem pow22_le {q n : ℕ} (hq : q ≤ n) (hn : 1 ≤ n) :
    (22 : ℝ) ^ q ≤ (1 + 10 * Real.exp 12 * (n : ℝ)) ^ n := by
  have h12 : (13 : ℝ) ≤ Real.exp 12 := by
    have := Real.add_one_le_exp (12 : ℝ); linarith
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h22 : (22 : ℝ) ≤ 1 + 10 * Real.exp 12 * (n : ℝ) := by nlinarith
  calc (22 : ℝ) ^ q ≤ 22 ^ n := pow_le_pow_right₀ (by norm_num) hq
    _ ≤ _ := pow_le_pow_left₀ (by norm_num) h22 n


/-! ### The signed second-case sheet bound with first-kind fixed and near-type rows -/

section WrapNear

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan Filter
  CatalanMeasure.GenD.Signed

/-- **Class-branch link data** (the Lemma K / Lemma T / `FixAdm` side of the consumer, supplied
with the class `Cls` of free configurations).  For the marked sheet with free rows `x`, marked
rows `y` (all in `G`) and a free class configuration `Cls N p x`:
* Lemma T for ALL positive nodes of the sheet (the exact conclusion of `lemmaT_of_slope`; no
  free-only form and no W term: Lemma 17.43.1 expands the marked positives);
* for every sign split of the free rows and of the marked rows: at least one free negative, more
  than `2g` free positives, the negative-fraction range of every α-interval containing
  `α = (m₁ + m₂')/n`, and for every splitting `τ` of the marked positives into first-kind and
  near rows, membership in `T.Clsf` and `T.FixAdm`.  The link is only asked for marked counts
`m ≤ α₁ n` (the hypothesis `hmle` of the consumer): for larger `m` the free-count clauses
(`2g < q`, the κ-range) are not true of the near-optimal class. -/
def SignedNearClassLinkNd (P : Parameters) {I : ℕ} (T : SignedNearBounds I)
    (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) (G : ℝ → Prop)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ (p m : ℕ) (hpm : p + m = P.n N), (m : ℝ) ≤ T.α1 * (T.ncount N : ℝ) →
    ∀ (x : Fin p → ℝ) (y : Fin m → ℝ),
    (∀ i, x i ∈ Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) → (∀ j, y j ∈ Ioo (-1 : ℝ) 1) →
    (∀ j, y j ≠ 0) → (∀ j, G (y j)) → Nd N m y → Function.Injective (Fin.append x y) →
    Cls N p x →
    (∀ c : Fin (P.n N) → ℝ,
      |∑ a ∈ Finset.univ.filter (fun a => 0 < sheetNodes hpm x y a),
        bDeriv (sheetNodes hpm x y) a * sheetNodes hpm x y a ^ (P.n N - 1 - 2 * P.g N) *
          c a ^ 2| ≤
        (3 / 2) * ∑ a, ∑ b, c a * c b /
          (1 - sheetNodes hpm x y a * sheetNodes hpm x y b)) ∧
    ∀ (k q m1 m2' : ℕ) (σx : Fin k ⊕ Fin q ≃ Fin p) (σy : Fin m1 ⊕ Fin m2' ≃ Fin m),
      (∀ b, x (σx (Sum.inl b)) < 0) → (∀ b, 0 < x (σx (Sum.inr b))) →
      (∀ b, y (σy (Sum.inl b)) < 0) → (∀ b, 0 < y (σy (Sum.inr b))) →
      0 < k ∧ 2 * P.g N < q ∧
      (∀ i, T.lo i ≤ ((m1 + m2' : ℕ) : ℝ) / (T.ncount N : ℝ) →
        ((m1 + m2' : ℕ) : ℝ) / (T.ncount N : ℝ) ≤ T.hi i →
        T.κlo i ≤ (k : ℝ) / (T.ncount N : ℝ) ∧ (k : ℝ) / (T.ncount N : ℝ) ≤ T.κhi i) ∧
      ∀ (r s' : ℕ) (τ : Fin r ⊕ Fin s' ≃ Fin m2'),
        T.Clsf N k q m1 (r + s') (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))
          (fun b => y (σy (Sum.inl b)))
          (Fin.append (fun j => y (σy (Sum.inr (τ (Sum.inl j)))))
            (fun j => y (σy (Sum.inr (τ (Sum.inr j)))))) ∧
        T.FixAdm N m1 r s' (fun b => y (σy (Sum.inl b)))
          (fun j => y (σy (Sum.inr (τ (Sum.inl j))))) (fun j => y (σy (Sum.inr (τ (Sum.inr j)))))

/-- The class link with no node-set restriction (`Nd` trivial). -/
def SignedNearClassLink (P : Parameters) {I : ℕ} (T : SignedNearBounds I)
    (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) (G : ℝ → Prop) : Prop :=
  SignedNearClassLinkNd P T Cls G (fun _ _ _ => True)

/-- `SignedSecondSheetCore` for marked rows restricted by a node-set predicate `Nd N m y`
(in the real assembly: `y = realCoordinate ∘ τ N ∘ a` for an injective `a`, see `MarkedCap.lean`). -/
def SignedSecondSheetCoreNd (P : Parameters) (G : ℝ → Prop)
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop) (target0 c2 alpha1 : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
    ∀ (p m : ℕ) (hpm : p + m = P.n N)
      (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (m : ℝ) ≤ alpha1 * (P.n N : ℝ) →
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Set.Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) → Nd N m y →
      (∀ i, s i ∈ Set.Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1 →
      markedSheetCore P N hpm x y s ≤
        5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m)

end WrapNear


section WrapNear2

open CatalanMeasure.GenD CatalanMeasure.GenD.Analytic OAI.InternalCatalan Filter
  CatalanMeasure.GenD.Signed

/-- **The signed second-case sheet bound with first-kind fixed and near-type rows (`α₁ > 0`)**:
`SignedSecondSheetCore` for the α-interval contract `SignedNearBounds`, from
* the non-class branch (`hnon`: the old energy route, restricted to the complement of `Cls`);
* the class branch: Lemma 17.43.1 (`abs_det_laurent_le_marked_expand`: Lemma T for ALL positives,
  the marked positives expanded over the subsets `S` and each term bounded through the near-type
  energy), the energy theorem `signed_second_energy_near_nodes` for the five lists of every
  splitting, and the EXACT row weights (`log_markedSheetWeight`, no row inequality: the fields
  `Rm = groupedMarkedField`, `Rn = groupedNearField` and the grouped constant at the actual
  counts), the cost being in `budgetFix` (`T.cost * n0 ≤ c2`);
* the identification of `T` with the sheet's data and the class link `hlink`.

This is the form with the non-class branch given directly for the factor-free core (`hnonC`):
the class `Cls` may then be defined by the factor-free product (S1, PROOF-RHO §2.5), so that
Lemma K is measured against the factor-free old route.  `signedSecondSheetNearNd` below is the
corollary with `hnon` for the grouped product with the factor. -/
theorem signedSecondSheetNearNd_core {P : Parameters} (hP : Admissible P) (G : ℝ → Prop)
    (target0 c2 : ℝ) (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) {I : ℕ}
    (T : SignedNearBounds I)
    (hn : ∀ N, T.ncount N = P.n N)
    (hconst : ∀ N r a b, r + a + b = P.n N →
      T.constant N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b)
    (hRf : ∀ N, T.Rf N = populationPhysicalFreeField P N)
    (hRm : ∀ N, T.Rm N = groupedMarkedField P N)
    (hRn : ∀ N, T.Rn N = groupedNearField P N)
    (hCf : ∀ N, T.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', T.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - P.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : T.B = -target0 + Real.log 2 / 2)
    (hcost : T.cost * (P.n0 : ℝ) ≤ c2)
    (hnonC : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      ∀ (p m : ℕ) (hpm : p + m = P.n N) (x : Fin p → ℝ) (y : Fin m → ℝ) (s : Fin p → ℝ),
      (∀ i, x i ∈ Set.Ioo (-1 : ℝ) 1) → (∀ i, x i ≠ 0) →
      (∀ j, y j ∈ Set.Ioo (-1 : ℝ) 1) → (∀ j, y j ≠ 0) → (∀ j, G (y j)) →
      (∀ i, s i ∈ Set.Ioo (0 : ℝ) 1) →
      Function.Injective (Fin.append x y) → Function.Injective s →
      (∑ i : Fin (p + m), paramCaseField P N (Fin.append x y i)) ≤ -1 →
      ¬ Cls N p x →
      markedSheetCore P N hpm x y s ≤
        5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
          Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m))
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hlink : SignedNearClassLinkNd P T Cls G Nd) :
    SignedSecondSheetCoreNd P G Nd target0 c2 T.α1 := by
  intro ε hε
  filter_upwards [hnonC ε hε,
    signed_second_energy_near_nodes T hε, hlink, eventually_gt_atTop (0 : ℕ)]
    with N hnonN hE hl hN0 p m hpm x y s hmle hx hx0 hy hy0 hyG hNd hs hzi hsi hcase
  by_cases hc : Cls N p x
  · -- class branch
    obtain ⟨hT, hrest⟩ := hl p m hpm (by rw [hn]; exact hmle) x y hx hx0 hy hy0 hyG hNd hzi hc
    obtain ⟨k, q, σx, hxneg, hxpos⟩ := exists_sign_split x hx0
    obtain ⟨m1, m2', σy, hyneg, hypos⟩ := exists_sign_split y hy0
    obtain ⟨hk, hq, hκ, hcl⟩ := hrest k q m1 m2' σx σy hxneg hxpos hyneg hypos
    have hkq := Fintype.card_congr σx
    simp only [Fintype.card_sum, Fintype.card_fin] at hkq
    have hm12 := Fintype.card_congr σy
    simp only [Fintype.card_sum, Fintype.card_fin] at hm12
    subst hkq
    have hn1 : 1 ≤ P.n N := n_pos hP hN0
    have hxi : Function.Injective x := by
      intro a b hab
      have := hzi (show Fin.append x y (Fin.castAdd m a) = Fin.append x y (Fin.castAdd m b) by
        simpa using hab)
      simpa using this
    have hyi : Function.Injective y := by
      intro a b hab
      have := hzi (show Fin.append x y (Fin.natAdd _ a) = Fin.append x y (Fin.natAdd _ b) by
        simpa using hab)
      simpa using this
    have hnR : (P.n N : ℝ) = (P.n0 : ℝ) * N := n_cast P N
    have hinjF : Function.Injective
        (Fin.append (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))) := by
      rw [append_split_eq]; exact hxi.comp (splitEquiv σx).injective
    have hcore := near_class_core_le hP hN0 hpm σx σy x s y hx hx0 hy hy0 hs hzi hsi hxneg hxpos
      hyneg hypos hk hq hT
      (-target0 + Real.log 2 / 2 + T.cost * ((m : ℝ) / (P.n N : ℝ)) + ε) (by
        intro r s' τ hinj
        obtain ⟨hCls, hAdm⟩ := hcl r s' τ
        have hM : r + s' = m2' := by simpa using (Fintype.card_congr τ)
        have hcnt : (k + m1) + (q + (r + s')) = T.ncount N := by rw [hn]; omega
        have hα : ((m1 + r + s' : ℕ) : ℝ) ≤ T.α1 * (T.ncount N : ℝ) := by
          have : m1 + r + s' = m := by omega
          rw [this, hn]; exact hmle
        have hκ' : ∀ i, T.lo i ≤ ((m1 + r + s' : ℕ) : ℝ) / (T.ncount N : ℝ) →
            ((m1 + r + s' : ℕ) : ℝ) / (T.ncount N : ℝ) ≤ T.hi i →
            T.κlo i ≤ (k : ℝ) / (T.ncount N : ℝ) ∧ (k : ℝ) / (T.ncount N : ℝ) ≤ T.κhi i := by
          have : m1 + r + s' = m1 + m2' := by omega
          rw [this]; exact hκ
        have hEc := hE k q m1 r s' hcnt hα hκ'
          (fun b => x (σx (Sum.inl b))) (fun b => x (σx (Sum.inr b)))
          (fun b => y (σy (Sum.inl b))) (fun j => y (σy (Sum.inr (τ (Sum.inl j)))))
          (fun j => y (σy (Sum.inr (τ (Sum.inr j))))) s
          (fun b => ⟨(hx _).1, hxneg b⟩) (fun b => ⟨hxpos b, (hx _).2⟩)
          (fun b => ⟨(hy _).1, hyneg b⟩) (fun j => ⟨hypos _, (hy _).2⟩)
          (fun j => ⟨hypos _, (hy _).2⟩) hinjF hinj
          (hyi.comp (σy.injective.comp (Sum.inr_injective.comp (τ.injective.comp Sum.inr_injective))))
          (fun j => hs j) hsi hCls hAdm
        have hcN : (m1 + r + s' : ℕ) = m := by omega
        have hconst' := hconst N (k + q) (m1 + r) s' (by omega)
        rw [hn] at hEc
        rw [hLRf, hconst', hRf, hRm, hRn, hCf, hB] at hEc
        have hαm : ((m1 + r + s' : ℕ) : ℝ) = (m : ℝ) := by exact_mod_cast hcN
        rw [hαm] at hEc
        unfold nearLHS
        linarith [hEc])
    have hq' : q + m2' ≤ P.n N := by omega
    have h22 := pow22_le hq' hn1
    have h5 : (1 : ℝ) ≤ 5 ^ m := one_le_pow₀ (by norm_num)
    have hmN : (0 : ℝ) ≤ (N : ℝ) * m := by positivity
    have hexp : Real.exp ((P.n N : ℝ) ^ 2 * (-target0 + Real.log 2 / 2 +
        T.cost * ((m : ℝ) / (P.n N : ℝ)) + ε)) ≤
        Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m) := by
      apply Real.exp_le_exp.mpr
      have hn0' : (P.n0 : ℝ) ≠ 0 := (n0_pos hP).ne'
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN0.ne'
      have e : (P.n N : ℝ) ^ 2 * (-target0 + Real.log 2 / 2 +
          T.cost * ((m : ℝ) / (P.n N : ℝ)) + ε) =
          ((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) +
            (T.cost * (P.n0 : ℝ)) * N * m := by
        rw [hnR]
        field_simp
        ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hcost hmN]
    calc markedSheetCore P N hpm x y s
        ≤ 22 ^ (q + m2') * Real.exp ((P.n N : ℝ) ^ 2 * (-target0 + Real.log 2 / 2 +
            T.cost * ((m : ℝ) / (P.n N : ℝ)) + ε)) := hcore
      _ ≤ (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
            Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m) :=
          mul_le_mul h22 hexp (Real.exp_pos _).le (by positivity)
      _ ≤ 5 ^ m * (1 + 10 * Real.exp 12 * (P.n N : ℝ)) ^ P.n N *
            Real.exp (((P.n0 : ℝ) * N) ^ 2 * (-target0 + Real.log 2 / 2 + ε) + c2 * N * m) := by
          rw [mul_assoc (5 ^ m : ℝ)]
          exact le_mul_of_one_le_left (mul_nonneg (by positivity) (Real.exp_pos _).le) h5
  · -- non-class branch
    exact hnonN p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hc

/-- `signedSecondSheetNearNd_core` with the non-class branch from the old energy route for the
grouped product WITH the factor `(∏ (1 + s_i))^m` (`hnon`), the factor being dropped (`≥ 1`). -/
theorem signedSecondSheetNearNd {P : Parameters} (hP : Admissible P) (G : ℝ → Prop)
    (target0 c2 : ℝ) (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) {I : ℕ}
    (T : SignedNearBounds I)
    (hn : ∀ N, T.ncount N = P.n N)
    (hconst : ∀ N r a b, r + a + b = P.n N →
      T.constant N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b)
    (hRf : ∀ N, T.Rf N = populationPhysicalFreeField P N)
    (hRm : ∀ N, T.Rm N = groupedMarkedField P N)
    (hRn : ∀ N, T.Rn N = groupedNearField P N)
    (hCf : ∀ N, T.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', T.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - P.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : T.B = -target0 + Real.log 2 / 2)
    (hcost : T.cost * (P.n0 : ℝ) ≤ c2)
    (hnon : GroupedMarkedProductCostOnRestr P target0 c2 G
      (fun N r _ _ z _ _ _ => ¬ Cls N r z))
    (Nd : ∀ (N m : ℕ), (Fin m → ℝ) → Prop)
    (hlink : SignedNearClassLinkNd P T Cls G Nd) :
    SignedSecondSheetCoreNd P G Nd target0 c2 T.α1 := by
  refine signedSecondSheetNearNd_core hP G target0 c2 Cls T hn hconst hRf hRm hRn hCf hLRf hB
    hcost ?_ Nd hlink
  intro ε hε
  filter_upwards [second_marked_sheet_product_on_restr hP target0 c2 G _ hnon hε]
    with N hnonN p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase hc
  · have hb := hnonN p m hpm x y s hx hx0 hy hy0 hyG hs hzi hsi hcase
      (fun _ _ _ _ => hc)
    rw [markedSheetProduct_eq_factor_mul_core] at hb
    have hf : (1 : ℝ) ≤ (∏ i, (1 + s i)) ^ m := by
      apply one_le_pow₀
      calc (1 : ℝ) = ∏ _i : Fin p, (1 : ℝ) := by simp
        _ ≤ ∏ i, (1 + s i) :=
          by gcongr with i _; linarith [(hs i).1]
    have hcnn : 0 ≤ markedSheetCore P N hpm x y s := by
      unfold markedSheetCore
      dsimp only
      exact div_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
        (Finset.prod_nonneg fun j _ => paramRowNodeWeight_nonneg P N (hy j)))
        (paramPinPrincipal_nonneg P N x s hx hs)) (Finset.prod_nonneg fun j _ => abs_nonneg _)
    exact (le_mul_of_one_le_left hcnn hf).trans hb


/-- The unrestricted statement (`Nd` trivial): `SignedSecondSheetCore` from `SignedNearClassLink`. -/
theorem signedSecondSheetNear {P : Parameters} (hP : Admissible P) (G : ℝ → Prop)
    (target0 c2 : ℝ) (Cls : ∀ (N r : ℕ), (Fin r → ℝ) → Prop) {I : ℕ}
    (T : SignedNearBounds I)
    (hn : ∀ N, T.ncount N = P.n N)
    (hconst : ∀ N r a b, r + a + b = P.n N →
      T.constant N (((a + b : ℕ) : ℝ) / (P.n N : ℝ)) = groupedConstant P N r a b)
    (hRf : ∀ N, T.Rf N = populationPhysicalFreeField P N)
    (hRm : ∀ N, T.Rm N = groupedMarkedField P N)
    (hRn : ∀ N, T.Rn N = groupedNearField P N)
    (hCf : ∀ N, T.Cf N = populationPhysicalColumnField P N (0 + 0))
    (hLRf : ∀ N k q m1 m2' xn gp yn yp', T.LRf N k q m1 m2' xn gp yn yp' =
      logRatioZ (q + m2' - P.g N) (Fin.append xn yn) (Fin.append gp yp'))
    (hB : T.B = -target0 + Real.log 2 / 2)
    (hcost : T.cost * (P.n0 : ℝ) ≤ c2)
    (hnon : GroupedMarkedProductCostOnRestr P target0 c2 G
      (fun N r _ _ z _ _ _ => ¬ Cls N r z))
    (hlink : SignedNearClassLink P T Cls G) :
    SignedSecondSheetCore P G target0 c2 T.α1 := by
  intro ε hε
  filter_upwards [signedSecondSheetNearNd hP G target0 c2 Cls T hn hconst hRf hRm hRn hCf hLRf hB
    hcost hnon (fun _ _ _ => True) hlink ε hε] with N h p m hpm x y s hmle hx hx0 hy hy0 hyG hs hzi
    hsi hcase
  exact h p m hpm x y s hmle hx hx0 hy hy0 hyG trivial hs hzi hsi hcase

end WrapNear2

end

end CatalanMeasure.Signed

#print axioms CatalanMeasure.Signed.logRatioZ_comp_pos
#print axioms CatalanMeasure.Signed.lamS_transport
#print axioms CatalanMeasure.Signed.exists_split_finset
#print axioms CatalanMeasure.Signed.pow22_le
#print axioms CatalanMeasure.Signed.near_split_data
#print axioms CatalanMeasure.Signed.sheetMarks_quad_free
#print axioms CatalanMeasure.Signed.sheetMarks_quad_marked
#print axioms CatalanMeasure.Signed.near_Sterm_le
#print axioms CatalanMeasure.Signed.near_class_core_le
#print axioms CatalanMeasure.Signed.signedSecondSheetNear
#print axioms CatalanMeasure.Signed.groupedConstant_split
#print axioms CatalanMeasure.Signed.log_msw_eq
#print axioms CatalanMeasure.Signed.near_field_eq
