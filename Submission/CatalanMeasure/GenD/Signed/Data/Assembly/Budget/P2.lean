module

public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.RowsCell
public import Submission.CatalanMeasure.GenD.Signed.Data.Assembly.Budget.P1

@[expose] public section

/-!
# 410 assembly: the cap data and the budget rows

The off-top and top-cell bounds of the fixed-row fields at the endpoint trials of each `α`-interval
are the threshold-table values `S_Lean` (rounded up to `2^-40`): chords in `α` of the corner values
for the positive field, bilinear interpolations in `(α, β)` (`bilin`) of the corner values for the
near field.  The log coefficients are `rP α = remC (1/10) α` and `rS = α / 2 + 10^-6`.

`zb410` bounds `zbCap` by `α max(ℓN, ℓP, ℓS) + C₁ (r_P e^{Bd/r_P} + r_S e^{Bd/r_S})`: the lines `ℓ`
are secants above the off-top chords, and `capInt c r θ ≤ r e^{Bd/r}` for a gap `c ≤ Bd < 0`.
The budget inequalities `hbudLo`, `hbudHi` are then, for each line, quadratic in `α` once the cap
term is bounded by a constant on each piece of the interval (`e^{-k} ≤ (3/8)^k`) and `log 2` by its
upper bound; each piece is closed by `quad_nonpos_Icc`.
-/

namespace CatalanMeasure.GenD.Signed.Data.Assembly
open Set Filter Topology
open CatalanMeasure.Signed CatalanMeasure.Signed.FieldForm OAI.InternalCatalan
open CatalanMeasure.Parametric CatalanMeasure.GenD CatalanMeasure.GenD.Analytic CatalanMeasure.GenD.D58

noncomputable section

namespace Bud410

/-! ### Generic lemmas -/


theorem cap1_1 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (31 / 1600 : ℝ)) : cap1 α ≤ (37385591169 / 1152921504606846976 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (341 / 12800 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (19377 / 2000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (341 / 12800 : ℝ)) 13 (47 / 341 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (19377 / 2000000 : ℝ)) 36 (2428 / 19377 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((341 / 12800 : ℝ) * ((3 / 8) ^ 13 * (1 / (1 + (47 / 341 : ℝ) + (47 / 341 : ℝ) ^ 2 / 2))) +
          (19377 / 2000000 : ℝ) * ((3 / 8) ^ 36 * (1 / (1 + (2428 / 19377 : ℝ) + (2428 / 19377 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (37385591169 / 1152921504606846976 : ℝ) := by norm_num

theorem cap1_2 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (17 / 640 : ℝ)) : cap1 α ≤ (848281655091 / 576460752303423488 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (187 / 5120 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (53129 / 4000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (187 / 5120 : ℝ)) 9 (109 / 187 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (53129 / 4000000 : ℝ)) 26 (18646 / 53129 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((187 / 5120 : ℝ) * ((3 / 8) ^ 9 * (1 / (1 + (109 / 187 : ℝ) + (109 / 187 : ℝ) ^ 2 / 2))) +
          (53129 / 4000000 : ℝ) * ((3 / 8) ^ 26 * (1 / (1 + (18646 / 53129 : ℝ) + (18646 / 53129 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (848281655091 / 576460752303423488 : ℝ) := by norm_num

theorem cap1_3 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (27 / 800 : ℝ)) : cap1 α ≤ (15907533320883 / 1152921504606846976 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (297 / 6400 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (4219 / 250000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (297 / 6400 : ℝ)) 7 (161 / 297 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (4219 / 250000 : ℝ)) 20 (3120 / 4219 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((297 / 6400 : ℝ) * ((3 / 8) ^ 7 * (1 / (1 + (161 / 297 : ℝ) + (161 / 297 : ℝ) ^ 2 / 2))) +
          (4219 / 250000 : ℝ) * ((3 / 8) ^ 20 * (1 / (1 + (3120 / 4219 : ℝ) + (3120 / 4219 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (15907533320883 / 1152921504606846976 : ℝ) := by norm_num

theorem cap1_4 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (131 / 3200 : ℝ)) : cap1 α ≤ (69993682689323 / 1152921504606846976 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (1441 / 25600 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (81879 / 4000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (1441 / 25600 : ℝ)) 6 (314 / 1441 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (81879 / 4000000 : ℝ)) 17 (1151 / 11697 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((1441 / 25600 : ℝ) * ((3 / 8) ^ 6 * (1 / (1 + (314 / 1441 : ℝ) + (314 / 1441 : ℝ) ^ 2 / 2))) +
          (81879 / 4000000 : ℝ) * ((3 / 8) ^ 17 * (1 / (1 + (1151 / 11697 : ℝ) + (1151 / 11697 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (69993682689323 / 1152921504606846976 : ℝ) := by norm_num

theorem cap1_5 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (77 / 1600 : ℝ)) : cap1 α ≤ (6396338832333 / 36028797018963968 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (847 / 12800 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (48127 / 2000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (847 / 12800 : ℝ)) 5 (35 / 121 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (48127 / 2000000 : ℝ)) 14 (26222 / 48127 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((847 / 12800 : ℝ) * ((3 / 8) ^ 5 * (1 / (1 + (35 / 121 : ℝ) + (35 / 121 : ℝ) ^ 2 / 2))) +
          (48127 / 2000000 : ℝ) * ((3 / 8) ^ 14 * (1 / (1 + (26222 / 48127 : ℝ) + (26222 / 48127 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (6396338832333 / 36028797018963968 : ℝ) := by norm_num

theorem cap1_6 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (177 / 3200 : ℝ)) : cap1 α ≤ (468348773017705 / 1152921504606846976 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (1947 / 25600 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (110629 / 4000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (1947 / 25600 : ℝ)) 4 (1172 / 1947 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (110629 / 4000000 : ℝ)) 12 (72452 / 110629 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((1947 / 25600 : ℝ) * ((3 / 8) ^ 4 * (1 / (1 + (1172 / 1947 : ℝ) + (1172 / 1947 : ℝ) ^ 2 / 2))) +
          (110629 / 4000000 : ℝ) * ((3 / 8) ^ 12 * (1 / (1 + (72452 / 110629 : ℝ) + (72452 / 110629 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (468348773017705 / 1152921504606846976 : ℝ) := by norm_num

theorem cap1_7 {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ (1 / 16 : ℝ)) : cap1 α ≤ (438839218052741 / 576460752303423488 : ℝ) := by
  unfold cap1
  have e1 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity) (show 11 / 8 * α ≤ (11 / 128 : ℝ) by linarith) (by norm_num)
  have e2 := cb_mono (Bd := (-7 / 20 : ℝ)) (by norm_num) (by positivity)
    (show α / 2 + 1 / 1000000 ≤ (31251 / 1000000 : ℝ) by linarith) (by norm_num)
  have n1 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (11 / 128 : ℝ)) 4 (4 / 55 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  have n2 := cb_le_num (Bd := (-7 / 20 : ℝ)) (R := (31251 / 1000000 : ℝ)) 11 (6239 / 31251 : ℝ) (by norm_num) (by norm_num) (by norm_num)
  calc (9631 / 20000 : ℝ) * (cb (-7 / 20 : ℝ) (11 / 8 * α) + cb (-7 / 20 : ℝ) (α / 2 + 1 / 1000000))
      ≤ 9631 / 20000 * ((11 / 128 : ℝ) * ((3 / 8) ^ 4 * (1 / (1 + (4 / 55 : ℝ) + (4 / 55 : ℝ) ^ 2 / 2))) +
          (31251 / 1000000 : ℝ) * ((3 / 8) ^ 11 * (1 / (1 + (6239 / 31251 : ℝ) + (6239 / 31251 : ℝ) ^ 2 / 2)))) := by
        gcongr
        · exact e1.trans n1
        · exact e2.trans n2
    _ ≤ (438839218052741 / 576460752303423488 : ℝ) := by norm_num

theorem bud1lo : ∀ α ∈ Icc (1 / 200 : ℝ) (1 / 16 : ℝ),
    interpCInf (1 / 200 : ℝ) (1 / 16 : ℝ) (Glue410.constantLim P410 α) (145423449 / 1000000000 : ℝ) (9020207 / 200000000 : ℝ) (181637 / 62500000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (27 / 100 : ℝ) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-1911012921633 / 1099511627776 : ℝ) (-939442945915 / 549755813888 : ℝ) α + (1 - (27 / 100 : ℝ) - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-466555285 / 268435456 : ℝ) (-917526653 / 536870912 : ℝ) α +
      (1 - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-858707041103 / 549755813888 : ℝ) (-816870426147 / 549755813888 : ℝ) α + zb1 α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α := by
  intro α hα
  have hl : interpL (1 / 200 : ℝ) (1 / 16 : ℝ) α = (α - (1 / 200 : ℝ)) / ((1 / 16 : ℝ) - (1 / 200 : ℝ)) := interpL_of_mem (by norm_num) hα.1 hα.2
  have hE : interpCInf (1 / 200 : ℝ) (1 / 16 : ℝ) (Glue410.constantLim P410 α) (145423449 / 1000000000 : ℝ) (9020207 / 200000000 : ℝ) (181637 / 62500000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (27 / 100 : ℝ) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-1911012921633 / 1099511627776 : ℝ) (-939442945915 / 549755813888 : ℝ) α + (1 - (27 / 100 : ℝ) - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-466555285 / 268435456 : ℝ) (-917526653 / 536870912 : ℝ) α +
      (1 - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-858707041103 / 549755813888 : ℝ) (-816870426147 / 549755813888 : ℝ) α -
      ((-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α) =
      (-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) := by
    rw [constLim410]
    simp only [interpCInf, chord, hl, fixLog2, K590.target0, K590.target, K590.secondCost']
    ring
  have hN : lineN1 α = (-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α := by simp only [lineN1, chord, hl]; ring
  have hP : lineP1 α = (-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α := by simp only [lineP1, chord, hl]; ring
  have hS : lineS1 α = (-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α := by simp only [lineS1, chord, hl]; ring
  have hF := F_nonneg1 hα
  have bN : (-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inr (Or.inr (Or.inr (by norm_num))))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inr (Or.inl (by norm_num)))
  have bP : (-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  have bS : (-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  have hz : zb1 α = α * max (lineN1 α) (max (lineP1 α) (lineS1 α)) + cap1 α := rfl
  rw [hN, hP, hS, mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1), mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1)] at hz
  have hm := max_le (show α * ((-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α) ≤ -((-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bN])
    (max_le (show α * ((-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α) ≤ -((-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bP])
      (show α * ((-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α) ≤ -((-3425775700163130828979477 / 3821567410700288000000000 : ℝ) + (-5965907560145466399 / 22720376995840000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bS]))
  linarith [hE, hz, hm]

theorem bud1hi : ∀ α ∈ Icc (1 / 200 : ℝ) (1 / 16 : ℝ),
    interpCInf (1 / 200 : ℝ) (1 / 16 : ℝ) (Glue410.constantLim P410 α) (145423449 / 1000000000 : ℝ) (9020207 / 200000000 : ℝ) (181637 / 62500000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (4431 / 10000 : ℝ) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-1911012921633 / 1099511627776 : ℝ) (-939442945915 / 549755813888 : ℝ) α + (1 - (4431 / 10000 : ℝ) - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-466555285 / 268435456 : ℝ) (-917526653 / 536870912 : ℝ) α +
      (1 - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-858707041103 / 549755813888 : ℝ) (-816870426147 / 549755813888 : ℝ) α + zb1 α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α := by
  intro α hα
  have hl : interpL (1 / 200 : ℝ) (1 / 16 : ℝ) α = (α - (1 / 200 : ℝ)) / ((1 / 16 : ℝ) - (1 / 200 : ℝ)) := interpL_of_mem (by norm_num) hα.1 hα.2
  have hE : interpCInf (1 / 200 : ℝ) (1 / 16 : ℝ) (Glue410.constantLim P410 α) (145423449 / 1000000000 : ℝ) (9020207 / 200000000 : ℝ) (181637 / 62500000 : ℝ) α + fixLog2 (1 / 10) α * Real.log 2 +
      (4431 / 10000 : ℝ) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-1911012921633 / 1099511627776 : ℝ) (-939442945915 / 549755813888 : ℝ) α + (1 - (4431 / 10000 : ℝ) - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-466555285 / 268435456 : ℝ) (-917526653 / 536870912 : ℝ) α +
      (1 - α) * chord (1 / 200 : ℝ) (1 / 16 : ℝ) (-858707041103 / 549755813888 : ℝ) (-816870426147 / 549755813888 : ℝ) α -
      ((-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α) =
      (-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) := by
    rw [constLim410]
    simp only [interpCInf, chord, hl, fixLog2, K590.target0, K590.target, K590.secondCost']
    ring
  have hN : lineN1 α = (-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α := by simp only [lineN1, chord, hl]; ring
  have hP : lineP1 α = (-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α := by simp only [lineP1, chord, hl]; ring
  have hS : lineS1 α = (-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α := by simp only [lineS1, chord, hl]; ring
  have hF := F_nonneg1 hα
  have bN : (-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inr (Or.inr (Or.inr (by norm_num))))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inr (Or.inl (by norm_num)))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inr (Or.inl (by norm_num)))
  have bP : (-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  have bS : (-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2) + α * ((-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α) + cap1 α ≤ 0 := by
    rcases le_total α (39 / 3200 : ℝ) with h0l | h0
    · exact bud_piece hα.1 h0l log2_le hF (cap1_0 (le_trans (by norm_num) hα.1) h0l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (31 / 1600 : ℝ) with h1l | h1
    · exact bud_piece h0 h1l log2_le hF (cap1_1 (le_trans (by norm_num) hα.1) h1l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (17 / 640 : ℝ) with h2l | h2
    · exact bud_piece h1 h2l log2_le hF (cap1_2 (le_trans (by norm_num) hα.1) h2l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (27 / 800 : ℝ) with h3l | h3
    · exact bud_piece h2 h3l log2_le hF (cap1_3 (le_trans (by norm_num) hα.1) h3l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (131 / 3200 : ℝ) with h4l | h4
    · exact bud_piece h3 h4l log2_le hF (cap1_4 (le_trans (by norm_num) hα.1) h4l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (77 / 1600 : ℝ) with h5l | h5
    · exact bud_piece h4 h5l log2_le hF (cap1_5 (le_trans (by norm_num) hα.1) h5l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    rcases le_total α (177 / 3200 : ℝ) with h6l | h6
    · exact bud_piece h5 h6l log2_le hF (cap1_6 (le_trans (by norm_num) hα.1) h6l) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
    exact bud_piece h6 hα.2 log2_le hF (cap1_7 (le_trans (by norm_num) hα.1) hα.2) (by norm_num) (by norm_num)
      (Or.inl (by norm_num))
  have hz : zb1 α = α * max (lineN1 α) (max (lineP1 α) (lineS1 α)) + cap1 α := rfl
  rw [hN, hP, hS, mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1), mul_max_of_nonneg _ _ (le_trans (by norm_num) hα.1)] at hz
  have hm := max_le (show α * ((-11199353369 / 24696061952 : ℝ) + (-328801575 / 1543503872 : ℝ) * α) ≤ -((-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bN])
    (max_le (show α * ((-322927167 / 536870912 : ℝ) + (85215725 / 33554432 : ℝ) * α) ≤ -((-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bP])
      (show α * ((-7292118403 / 12348030976 : ℝ) + (1124371275 / 385875968 : ℝ) * α) ≤ -((-13703152945633685472946033 / 15286269642801152000000000 : ℝ) + (-11905542548091460923 / 45440753991680000000 : ℝ) * α + (-13480394098868793 / 14200235622400000 : ℝ) * α ^ 2 + Real.log 2 * ((75 / 58 : ℝ) + (621 / 580 : ℝ) * α + (-69 / 80 : ℝ) * α ^ 2)) - cap1 α by linarith [bS]))
  linarith [hE, hz, hm]

/-! ### The endpoint suprema and constants of the table, and the budget rows -/

def SnA410 : Fin 2 → ℝ := ![(-1913689396221 / 1099511627776 : ℝ), (-1911012921633 / 1099511627776 : ℝ)]
def SnB410 : Fin 2 → ℝ := ![(-1911012921633 / 1099511627776 : ℝ), (-939442945915 / 549755813888 : ℝ)]
def SpA410 : Fin 2 → ℝ := ![(-1868836503 / 1073741824 : ℝ), (-466555285 / 268435456 : ℝ)]
def SpB410 : Fin 2 → ℝ := ![(-466555285 / 268435456 : ℝ), (-917526653 / 536870912 : ℝ)]
def SyA410 : Fin 2 → ℝ := ![(-1724586542717 / 1099511627776 : ℝ), (-858707041103 / 549755813888 : ℝ)]
def SyB410 : Fin 2 → ℝ := ![(-858707041103 / 549755813888 : ℝ), (-816870426147 / 549755813888 : ℝ)]
def rAq : Fin 2 → ℝ := ![(30870737 / 200000000 : ℝ), (145423449 / 1000000000 : ℝ)]
def rBq : Fin 2 → ℝ := ![(145423449 / 1000000000 : ℝ), (9020207 / 200000000 : ℝ)]
def κcq : Fin 2 → ℝ := ![(14003 / 1000000000 : ℝ), (181637 / 62500000 : ℝ)]

theorem hbudLo410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i),
    interpCInf (αA410 i) (αB410 i) (Glue410.constantLim P410 α) (rAq i) (rBq i) (κcq i) α +
      fixLog2 (1 / 10) α * Real.log 2 +
      κlo410 i * chord (αA410 i) (αB410 i) (SnA410 i) (SnB410 i) α +
      (1 - κlo410 i - α) * chord (αA410 i) (αB410 i) (SpA410 i) (SpB410 i) α +
      (1 - α) * chord (αA410 i) (αB410 i) (SyA410 i) (SyB410 i) α + ![zb0, zb1] i α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α :=
  Fin.forall_fin_two.2 ⟨bud0lo, bud1lo⟩

theorem hbudHi410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i),
    interpCInf (αA410 i) (αB410 i) (Glue410.constantLim P410 α) (rAq i) (rBq i) (κcq i) α +
      fixLog2 (1 / 10) α * Real.log 2 +
      κhi410 i * chord (αA410 i) (αB410 i) (SnA410 i) (SnB410 i) α +
      (1 - κhi410 i - α) * chord (αA410 i) (αB410 i) (SpA410 i) (SpB410 i) α +
      (1 - α) * chord (αA410 i) (αB410 i) (SyA410 i) (SyB410 i) α + ![zb0, zb1] i α ≤
        (-K590.target0 + Real.log 2 / 2) + K590.secondCost' * α :=
  Fin.forall_fin_two.2 ⟨bud0hi, bud1hi⟩

/-! ### The `Rows410` fields -/

def capE410 : Fin 2 → CapEnd := ![capE0, capE1]
def zb410 : Fin 2 → ℝ → ℝ := ![zb0, zb1]
def Bd410 : Fin 2 → ℝ := ![(-19 / 50 : ℝ), (-7 / 20 : ℝ)]
def Rbd410 : Fin 2 → ℝ := ![(11 / 1600 : ℝ), (11 / 128 : ℝ)]

theorem hxc0_410 : ∀ i, 0 ≤ (capE410 i).xc :=
  Fin.forall_fin_two.2 ⟨by show (0 : ℝ) ≤ 999 / 1000; norm_num, by show (0 : ℝ) ≤ 999 / 1000; norm_num⟩

theorem hxc1_410 : ∀ i, (capE410 i).xc < 1 :=
  Fin.forall_fin_two.2 ⟨by show (999 / 1000 : ℝ) < 1; norm_num, by show (999 / 1000 : ℝ) < 1; norm_num⟩

theorem hC1_410 : ∀ i, 0 < (capE410 i).C1 :=
  Fin.forall_fin_two.2 ⟨by show (0 : ℝ) < 9631 / 20000; norm_num, by show (0 : ℝ) < 9631 / 20000; norm_num⟩

theorem hgs410 : ∀ i, (capE410 i).gs ≤ 401 / 2500 :=
  Fin.forall_fin_two.2 ⟨le_refl _, le_refl _⟩

theorem hxc410 : ∀ i, 999 / 1000 ≤ (capE410 i).xc :=
  Fin.forall_fin_two.2 ⟨le_refl _, le_refl _⟩

theorem hC1le410 : ∀ i, 9631 / 20000 ≤ (capE410 i).C1 :=
  Fin.forall_fin_two.2 ⟨le_refl _, le_refl _⟩

theorem hrP410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), remC (1 / 10) * α ≤ (capE410 i).rP α :=
  Fin.forall_fin_two.2 ⟨fun α _ => by show remC (1 / 10) * α ≤ 11 / 8 * α; norm_num [remC],
    fun α _ => by show remC (1 / 10) * α ≤ 11 / 8 * α; norm_num [remC]⟩

theorem hrSA410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, 0 ≤ (capE410 i).rSA α β :=
  Fin.forall_fin_two.2 ⟨fun α _ β hβ => by show (0 : ℝ) ≤ α / 2 + 1 / 1000000; linarith [hβ.1, hβ.2],
    fun α _ β hβ => by show (0 : ℝ) ≤ α / 2 + 1 / 1000000; linarith [hβ.1, hβ.2]⟩

theorem hrSB410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, 0 ≤ (capE410 i).rSB α β :=
  Fin.forall_fin_two.2 ⟨fun α _ β hβ => by show (0 : ℝ) ≤ α / 2 + 1 / 1000000; linarith [hβ.1, hβ.2],
    fun α _ β hβ => by show (0 : ℝ) ≤ α / 2 + 1 / 1000000; linarith [hβ.1, hβ.2]⟩

theorem hBdPA410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE410 i).gPA α - (capE410 i).lamPA α ≤ Bd410 i :=
  Fin.forall_fin_two.2 ⟨fun α _ => (gapP0 α).1, fun α _ => (gapP1 α).1⟩

theorem hBdPB410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE410 i).gPB α - (capE410 i).lamPB α ≤ Bd410 i :=
  Fin.forall_fin_two.2 ⟨fun α _ => (gapP0 α).2, fun α _ => (gapP1 α).2⟩

theorem hBdSA410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α,
    (capE410 i).gSA α β - (capE410 i).lamSA α β ≤ Bd410 i :=
  Fin.forall_fin_two.2 ⟨fun _ hα _ hβ => (gapS0 hα hβ).1, fun _ hα _ hβ => (gapS1 hα hβ).1⟩

theorem hBdSB410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α,
    (capE410 i).gSB α β - (capE410 i).lamSB α β ≤ Bd410 i :=
  Fin.forall_fin_two.2 ⟨fun _ hα _ hβ => (gapS0 hα hβ).2, fun _ hα _ hβ => (gapS1 hα hβ).2⟩

theorem hRP410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), (capE410 i).rP α ≤ Rbd410 i :=
  Fin.forall_fin_two.2
    ⟨fun α hα => by
      have h2 : α ≤ 1 / 200 := hα.2
      show 11 / 8 * α ≤ (11 / 1600 : ℝ); linarith,
     fun α hα => by
      have h2 : α ≤ 1 / 16 := hα.2
      show 11 / 8 * α ≤ (11 / 128 : ℝ); linarith⟩

theorem hRSA410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, (capE410 i).rSA α β ≤ Rbd410 i :=
  Fin.forall_fin_two.2
    ⟨fun α hα _ _ => by
      have h2 : α ≤ 1 / 200 := hα.2
      show α / 2 + 1 / 1000000 ≤ (11 / 1600 : ℝ); linarith,
     fun α hα _ _ => by
      have h2 : α ≤ 1 / 16 := hα.2
      show α / 2 + 1 / 1000000 ≤ (11 / 128 : ℝ); linarith⟩

theorem hRSB410 : ∀ i, ∀ α ∈ Icc (lo410 i) (hi410 i), ∀ β ∈ Icc 0 α, (capE410 i).rSB α β ≤ Rbd410 i :=
  Fin.forall_fin_two.2
    ⟨fun α hα _ _ => by
      have h2 : α ≤ 1 / 200 := hα.2
      show α / 2 + 1 / 1000000 ≤ (11 / 1600 : ℝ); linarith,
     fun α hα _ _ => by
      have h2 : α ≤ 1 / 16 := hα.2
      show α / 2 + 1 / 1000000 ≤ (11 / 128 : ℝ); linarith⟩

theorem hZB410 : ∀ (i : Fin 2) (c d e : ℝ), 0 ≤ c → 0 ≤ d → 0 ≤ e → lo410 i ≤ c + d + e →
    c + d + e ≤ hi410 i →
    zbCap ((capE410 i).toS (αA410 i) (αB410 i)) c d e ≤ zb410 i (c + d + e) :=
  Fin.forall_fin_two.2 ⟨hZB0, hZB1⟩

end Bud410

end

end CatalanMeasure.GenD.Signed.Data.Assembly
