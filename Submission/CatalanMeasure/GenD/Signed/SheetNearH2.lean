module

public import Submission.CatalanMeasure.GenD.Signed.EnergyNear
public import Submission.CatalanMeasure.GenD.Signed.MarkedExpansion
public import Submission.CatalanMeasure.GenD.Signed.RealPlaceFixed
public import Submission.CatalanMeasure.GenD.Signed.SheetNearH1

/-! This module is a continuation shard of `SheetNear` (`catalan-410` peak-RSS split); statements are unchanged. -/

@[expose] public section

namespace CatalanMeasure.Signed

open Set Finset
open scoped BigOperators
open CatalanMeasure.Parametric

noncomputable section

set_option maxRecDepth 100000
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

end
end CatalanMeasure.Signed
