module
public import Submission.CatalanMeasure.QuadCircle
public import Mathlib.Analysis.Complex.ExponentialBounds
@[expose] public section
namespace CatalanMeasure.Parametric
noncomputable section
def residualRadius : ℚ := 1001 / 1000
@[irreducible] def residualCircleK : ℚ := 10^65
def residualCirclePieces : List (ℚ × ℚ × ℚ) := [((1 / 1000 : ℚ), (1001 / 1000 : ℚ), (173435983 / 100000000 : ℚ)),
  ((1001 / 1000 : ℚ), (1501 / 1000 : ℚ), (229346987 / 100000000 : ℚ)),
  ((1501 / 1000 : ℚ), (813 / 500 : ℚ), (60730599 / 25000000 : ℚ)),
  ((813 / 500 : ℚ), (3377 / 2000 : ℚ), (49933597 / 20000000 : ℚ)),
  ((3377 / 2000 : ℚ), (1751 / 1000 : ℚ), (32048557 / 12500000 : ℚ)),
  ((1751 / 1000 : ℚ), (7129 / 4000 : ℚ), (259739881 / 100000000 : ℚ)),
  ((7129 / 4000 : ℚ), (14383 / 8000 : ℚ), (26141349 / 10000000 : ℚ)),
  ((14383 / 8000 : ℚ), (3627 / 2000 : ℚ), (263085733 / 100000000 : ℚ)),
  ((3627 / 2000 : ℚ), (14633 / 8000 : ℚ), (132378317 / 50000000 : ℚ)),
  ((14633 / 8000 : ℚ), (7379 / 4000 : ℚ), (13321311 / 5000000 : ℚ)),
  ((7379 / 4000 : ℚ), (14883 / 8000 : ℚ), (53618903 / 20000000 : ℚ)),
  ((14883 / 8000 : ℚ), (469 / 250 : ℚ), (269761543 / 100000000 : ℚ)),
  ((469 / 250 : ℚ), (7629 / 4000 : ℚ), (273091891 / 100000000 : ℚ)),
  ((7629 / 4000 : ℚ), (3877 / 2000 : ℚ), (276417443 / 100000000 : ℚ)),
  ((3877 / 2000 : ℚ), (2001 / 1000 : ℚ), (70763709 / 25000000 : ℚ))]
def residualCirclePieceOK (p : ℚ × ℚ × ℚ) : Bool :=
  decide (0 ≤ p.1) && decide (p.1 ≤ p.2.1) && decide (p.2.1 ≤ residualRadius+1) &&
  decide (0 ≤ p.2.2) && decide ((residualRadius+p.2.1)^2-1 ≤ p.2.2^2) &&
  decide ((residualRadius+p.2.1+p.2.2)^89 *
    (2*(residualRadius^2+1)-p.1^2)^6 * residualRadius^14 ≤ residualCircleK)
def residualCircleCovers : ℚ → List (ℚ × ℚ × ℚ) → Bool
  | c, [] => decide (c = residualRadius+1)
  | c, p::l => decide (p.1=c) && residualCirclePieceOK p && residualCircleCovers p.2.1 l

theorem residualCircle_endpoint :
    ((residualRadius:ℝ)+(residualRadius+1)+
      Real.sqrt (((residualRadius:ℝ)+(residualRadius+1))^2-1))^89 *
      (2*((residualRadius:ℝ)^2+1)-(residualRadius+1)^2)^6 *
      (residualRadius:ℝ)^14 ≤ (residualCircleK:ℝ) := by
  have hs : Real.sqrt (((residualRadius:ℝ)+(residualRadius+1))^2-1) ≤ 3 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num [residualRadius]
  calc _ ≤ ((residualRadius:ℝ)+(residualRadius+1)+3)^89 *
      (2*((residualRadius:ℝ)^2+1)-(residualRadius+1)^2)^6 *
      (residualRadius:ℝ)^14 := by
        gcongr
        norm_num [residualRadius] <;> positivity
    _ ≤ (residualCircleK:ℝ) := by norm_num [residualRadius,residualCircleK]

theorem residualCircleCovers_spec {c : ℚ} {l : List (ℚ × ℚ × ℚ)}
    (h : residualCircleCovers c l = true) {s : ℝ}
    (hs : (c:ℝ) ≤ s) (hs2 : s ≤ (residualRadius:ℝ)+1) :
    ((residualRadius:ℝ)+s+Real.sqrt (((residualRadius:ℝ)+s)^2-1))^89 *
      (2*((residualRadius:ℝ)^2+1)-s^2)^6 * (residualRadius:ℝ)^14 ≤
      (residualCircleK:ℝ) := by
  induction l generalizing c with
  | nil =>
    simp only [residualCircleCovers,decide_eq_true_eq] at h
    subst h
    have he : s = (residualRadius:ℝ)+1 := by
      push_cast at hs
      linarith
    rw [he]
    exact residualCircle_endpoint
  | cons p l ih =>
    simp only [residualCircleCovers,residualCirclePieceOK,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨hc,⟨⟨⟨⟨⟨h0,h01⟩,h12⟩,hu0⟩,hu⟩,hK⟩⟩,hrest⟩ := h
    subst hc
    by_cases hs1 : s ≤ p.2.1
    · have hs0 : 0 ≤ s := le_trans (by exact_mod_cast h0) hs
      have hr0 : (0:ℝ) ≤ residualRadius := by norm_num [residualRadius]
      have hp0 : (0:ℝ) ≤ p.1 := by exact_mod_cast h0
      have hsq : Real.sqrt (((residualRadius:ℝ)+s)^2-1) ≤ p.2.2 := by
        rw [Real.sqrt_le_left (by exact_mod_cast hu0)]
        have hh : ((residualRadius:ℝ)+(p.2.1:ℝ))^2-1 ≤ (p.2.2:ℝ)^2 := by exact_mod_cast hu
        nlinarith
      have hA : (residualRadius:ℝ)+s+Real.sqrt (((residualRadius:ℝ)+s)^2-1) ≤
          (residualRadius:ℝ)+p.2.1+p.2.2 := by linarith
      have hB : (2*((residualRadius:ℝ)^2+1)-s^2)^6 ≤
          (2*((residualRadius:ℝ)^2+1)-(p.1:ℝ)^2)^6 := by
        apply pow_le_pow_left₀
        · have hsend := hs2
          norm_num [residualRadius] at hsend ⊢
          nlinarith
        · nlinarith
      have hK' : ((residualRadius:ℝ)+(p.2.1:ℝ)+p.2.2)^89 *
          (2*((residualRadius:ℝ)^2+1)-(p.1:ℝ)^2)^6 *
          (residualRadius:ℝ)^14 ≤ (residualCircleK:ℝ) := by exact_mod_cast hK
      calc _ ≤ ((residualRadius:ℝ)+(p.2.1:ℝ)+p.2.2)^89 *
          (2*((residualRadius:ℝ)^2+1)-(p.1:ℝ)^2)^6 * (residualRadius:ℝ)^14 := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            apply mul_le_mul
            · exact pow_le_pow_left₀ (by positivity) hA 89
            · exact hB
            · positivity
            · have hp1 : (0:ℝ) ≤ p.2.1 := le_trans hs0 hs1
              have hp2 : (0:ℝ) ≤ p.2.2 := by exact_mod_cast hu0
              positivity
        _ ≤ (residualCircleK:ℝ) := hK'
    · exact ih hrest (le_of_lt (not_le.mp hs1))

set_option maxRecDepth 4000 in
set_option maxHeartbeats 800000 in
theorem residualCircleCovers_true :
    residualCircleCovers (residualRadius-1) residualCirclePieces = true := by decide +kernel

/-- Exact uniform radius certificate for the restricted 89N-dimensional row space. -/
theorem residualCircle_ineq {s : ℝ} (hs0 : (residualRadius:ℝ)-1 ≤ s)
    (hs2 : s ≤ (residualRadius:ℝ)+1) :
    ((residualRadius:ℝ)+s+Real.sqrt (((residualRadius:ℝ)+s)^2-1))^89 *
      (2*((residualRadius:ℝ)^2+1)-s^2)^6 * (residualRadius:ℝ)^14 ≤
      (residualCircleK:ℝ) :=
  residualCircleCovers_spec residualCircleCovers_true (by simpa using hs0) hs2

theorem residualCircleK_le_exp : (residualCircleK:ℝ) ≤ Real.exp 150 := by
  have he : (2.7182818283:ℝ) ≤ Real.exp 1 := Real.exp_one_gt_d9.le
  rw [show (150:ℝ) = (150:ℕ)*1 by norm_num,Real.exp_nat_mul]
  calc (residualCircleK:ℝ) ≤ (2.7182818283:ℝ)^150 := by norm_num [residualCircleK]
    _ ≤ Real.exp 1 ^150 := pow_le_pow_left₀ (by norm_num) he 150
end
end CatalanMeasure.Parametric
